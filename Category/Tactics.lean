import Qq
import Lean

import Lean.Data.RBMap
import Lean.Data.RBTree
import Category.Basic
import Category.UnionFind

open Lean Lean.Expr Lean.Meta Lean.Elab.Tactic

open Qq

universe u v

structure Result {α:Q(Type u)} (E: Q($α) → Type) (e: Q($α)) where
  expr  : Q($α)
  val   : E expr
  proof : Q($e = $expr)

def Result.Id {α:Q(Type u)} {E:Q($α) → Type} (e: Q($α)) (val: E e) : Result E e where
  expr  := e
  val   := val
  proof := q(by rfl)

def Result.map {α:Q(Type u)} {E:Q($α) → Type} {e: Q($α)}
  (r:Result E e) (F:Q($α) → Type) (f: E r.expr → F r.expr) : Result F e where
  expr  := r.expr
  val   := f r.val
  proof := r.proof

instance [Inhabited (Σ e, E e)] : Inhabited (Result E e) :=
  let ⟨e', v⟩ : Σ e, E e := default; ⟨e', v, default⟩

section

variable (α:Q(Sort u))

inductive QEquality (x y:Q($α)) : Prop where
| intro : Q($x = $y) → QEquality x y

def QEquivalence : Equivalence (QEquality α) where
  refl := by
    intro x
    apply QEquality.intro
    exact q(by rfl)

  symm := by
    intro x y xy
    cases xy with
    | intro eq =>
      apply QEquality.intro
      exact q(Eq.symm «$eq»)

  trans := by
    intro x y z xy yz
    cases xy
    cases yz
    case intro.intro xy yz =>
      apply QEquality.intro
      exact q(Eq.trans «$xy» «$yz»)

def QSetoid : Setoid Q($α) where
  r := QEquality α
  iseqv := QEquivalence α

instance {α:Q(Sort u)} : Setoid Q($α) := QSetoid α

-- lean doesn't infer the instance, I don't know why, probably because of level inference
instance {C:Q(Type u)} {_:Q(Category.{u, v} $C)} {X Y:Q($C)} :
  Setoid Q($X ⟶  $Y) := @QSetoid (Level.succ v) q($X ⟶  $Y)

end

namespace Cat

structure Context where
  useTransparancy : Bool

#print Ordering

def Nat.cmp (x y:Nat) : Ordering :=
  if x < y then Ordering.lt else if y < x then Ordering.gt else Ordering.eq

def PairNat.cmp (p₁ p₂:Nat × Nat) : Ordering :=
  match Nat.cmp p₁.fst p₂.fst with
  | Ordering.eq =>
    Nat.cmp p₁.snd p₂.snd
  | o => o

structure State where
  atoms : Array Expr := #[]
  u : Level := Level.zero
  v : Level := Level.zero
  C : Q(Type u)
  inst : Q(Category.{u, v} $C)
  obj : Array Q($C)
  arrow : RBMap (Nat × Nat) (
    Σ
      (X Y:Q($C))
      (size:Nat)
      (vec: Vector Q($X ⟶  $Y) size),
      Option <| UnionFind size vec
  ) PairNat.cmp


instance : Inhabited State where
  default := ⟨#[], Level.succ Level.zero, Level.zero, q(Type), q(inferInstanceAs (Category Type)), #[], RBMap.empty⟩

abbrev CatM := ReaderT Context <| StateT State MetaM

def CatM.run {α:Type} (f:CatM α) (red:Bool) :
  MetaM α := (f ⟨red⟩).run' default

#check inferType
#check @Category.Hom

def CatM.add_atom (e:Expr) : CatM Nat := do
  let table ← get
  if (← read).useTransparancy then
    for h : i in [0:table.atoms.size] do
      have : i < table.atoms.size := h.2
      if ← isDefEq e table.atoms[i] then
        return i
  modifyGet fun c => (table.atoms.size, {c with atoms := c.atoms.push e})

def CatM.add_obj (e:Expr) : CatM Nat := do
  let table ← get
  for h : i in [0:table.obj.size] do
      have : i < table.obj.size := h.2
      if ← isDefEq e table.obj[i] then
        return i
  modifyGet fun c => (table.obj.size, {c with obj := c.obj.push e})


def CatM.match_arrow (f:Expr) : CatM (Expr × Expr) := do
  let state ← get
  match state with
  | State.mk _ _ v C _ _ _ =>
    let type_f : Expr ← whnf (← inferType f)
    have type_f : Q(Type v) := type_f
    match type_f with
    | ~q(@Category.Hom «$C» _ $X $Y) =>
      return (X, Y)
    | _ =>
      throwError "match_arrow: not a morphism"


def CatM.add_arrow (domIdx codIdx:Nat) (f:Expr) : CatM Unit := do
  let state ← get
  match state with
  | State.mk atoms u v C _ obj arrow =>
    match RBMap.find? arrow (domIdx, codIdx) with
    | some ⟨X, Y, size, vec, none⟩ =>
      let (X', Y') ← match_arrow f

      if not (← isDefEq X X') then throwError "add_arrow: bad domain"
      if not (← isDefEq Y Y') then throwError "add_arrow: bad codomain"

      have f : Q($X ⟶  $Y) := f

      for h : i  in [0:size] do
        have : i < size := h.2
        if ← isDefEq f vec[i] then return ()

      modify fun _ => ⟨atoms, u, v, C, _, obj,
        /- *** force the reference counting of vec to 1 *** -/
        let arrow := arrow.insert (domIdx, codIdx) ⟨X, Y, 0, ⟨#[], by simp⟩, none⟩
        let vec: Vector Q($X ⟶  $Y) (Nat.succ size) := vec.push f
        arrow.insert (domIdx, codIdx) ⟨X, Y, Nat.succ size, vec, none⟩
      ⟩
    | none =>
      let some X := obj.get? domIdx | throwError "out of bound"
      let some Y := obj.get? codIdx | throwError "out of bound"
      let (X', Y') ← match_arrow f

      if not (← isDefEq X X') then throwError "add_arrow: bad domain"
      if not (← isDefEq Y Y') then throwError "add_arrow: bad codomain"

      have X : Q($C) := X; have Y : Q($C) := Y
      have f : Q($X ⟶  $Y) := f

      modify fun _ => ⟨atoms, u, v, C, _, obj, arrow.insert (domIdx, codIdx) ⟨X, Y, 1, ⟨#[f], by simp⟩, none⟩⟩
    | _ =>
      throwError "add_arrow: the unin find shound be empty"

section

variable {C: Q(Type u)}
variable {CatC: Q(Category.{u, v} $C)}

inductive Atom : ∀ X Y: Q($C), Q($X ⟶  $Y) → Type where
| Const : ∀ X Y: Q($C), ∀ f: Q($X ⟶  $Y), Nat → Atom X Y f
| Id : ∀ X: Q($C), Atom X X q(𝟙 $X)

inductive Morphism : ∀ X Y: Q($C), Q($X ⟶  $Y) → Type where
| Nil : ∀ {X Y f}, Atom X Y f → Morphism X Y f
| Cons: ∀ {X Z: Q($C)} (Y:Q($C)),
  ∀ f: Q($Y ⟶  $Z), ∀ g: Q($X ⟶  $Y),
  Atom Y Z f → Morphism X Y g → Morphism X Z q($f ⊚ $g)


instance {X Y:Q($C)} {f:Q($X ⟶  $Y)} : Inhabited (@Morphism u v C CatC X Y f) where
  default := Morphism.Nil <| Atom.Const X Y f 0

instance {X Y:Q($C)} : Inhabited (Σ f, @Morphism u v C CatC X Y f) where
  default := ⟨default, default⟩


#check Result


def Morphism.compose {X Y Z: Q($C)} (f1:Q($Y ⟶  $Z)) (f2:Q($X ⟶  $Y))
  (l1:Morphism Y Z f1) (l2:Morphism X Y f2) :
    @Result _ q($X ⟶  $Z) (@Morphism _ _ C CatC X Z) q($f1 ⊚ $f2) :=
    match (l1, l2) with
    | (l1, Morphism.Nil (Atom.Id _)) =>
      {
        expr  := f1,
        val   := l1,
        proof := q(by
          simp
        )
      }
    | (Morphism.Nil (Atom.Id _), l2) =>
      {
        expr  := f2,
        val   := l2,
        proof := q(by
          simp
        )
      }
    | (Morphism.Nil atom, l2) =>
      {
        expr  := q($f1 ⊚ $f2),
        val   := Morphism.Cons Y f1 f2 atom l2
        proof := q(by simp)
      }
    | (Morphism.Cons Z f1 g1 atom l1, l2) =>
      match compose g1 f2 l1 l2 with
      | Result.mk expr val proof =>
        {
          expr  := q($f1 ⊚ $expr)
          val   := Morphism.Cons Z f1 expr atom val,
          proof := q(by
            simp only [«$proof», Category.assoc]
          )
       }



-- \f<< for « and \f>> for »
mutual

partial def match_morphism_dom_eq_cod (X: Q($C)) (f:Q($X ⟶  $X)) :
  CatM (@Result _ q($X ⟶  $X) (@Morphism _ _ C CatC X X) f) := do

  match f with
  | ~q(𝟙 «$X») => do
    return {expr := q(𝟙 $X), val := Morphism.Nil (Atom.Id X), proof := q(by rfl)}
  | ~q(@Category.comp _ _ _ «$X» _ $g $h) => do
    let r1 ← @match_morphism_dom_eq_cod X g
    let r2 ← match_morphism_dom_eq_cod X h

    match (r1, r2) with
    | (Result.mk g' val_g proof_g, Result.mk h' val_h proof_h) =>
      match Morphism.compose g' h' val_g val_h with
      | Result.mk expr val proof =>
      return {
        expr := expr, --q($g' ⊚ $h'),
        val := val,
        proof := q(by
          rw [<-«$proof», <-«$proof_g», <-«$proof_h»]
        )
      }
  | ~q(@Category.comp _ _ _ $Y _ $g $h) => do
    let r1 ← match_morphism Y X g
    let r2 ← match_morphism X Y h

    match (r1, r2) with
    | (Result.mk g' val_g proof_g, Result.mk h' val_h proof_h) =>
      match Morphism.compose g' h' val_g val_h with
      | Result.mk expr val proof =>
        return {
          expr := expr,
          val := val,
          proof := q(by
            rw [<-«$proof», <-«$proof_g», <-«$proof_h»]
          )
        }
  | _ =>
    let idx ← CatM.add_atom f
    return Result.Id f <| Morphism.Nil (Atom.Const X X f idx)



-- patern match a morphism when the codomain and the domain are distincts
partial def match_morphism (X Y: Q($C)) (f:Q($X ⟶  $Y)) :
  CatM (@Result _ q($X ⟶  $Y) (@Morphism _ _ C CatC X Y) f) := do

  match f with
  | ~q(@Category.comp _ _ _ «$X» _ $g $h) =>
    let r2 ← match_morphism_dom_eq_cod X h
    let r1 ← match_morphism X Y g

    match (r1, r2) with
    | (Result.mk g' val_g proof_g, Result.mk h' val_h proof_h) =>
      match Morphism.compose g' h' val_g val_h with
      | Result.mk expr val proof =>
        return {
          expr := expr,
          val  := val,
          proof:= q(by
            rw [<-«$proof», <-«$proof_g», <-«$proof_h»]
          )
        }
  | ~q(@Category.comp _ _ _ «$Y» _ $g $h) =>
    let r1 ← match_morphism_dom_eq_cod Y g
    let r2 ← match_morphism X Y h

    match (r1, r2) with
    | (Result.mk g' val_g proof_g, Result.mk h' val_h proof_h) =>
      match Morphism.compose g' h' val_g val_h with
      | Result.mk expr val proof =>
        return {
          expr := expr,
          val  := val,
          proof:= q(by
            rw [<-«$proof», <-«$proof_g», <-«$proof_h»]
          )
        }
  | ~q(@Category.comp _ _ _ $Z _ $g $h) =>
    let r2 ← match_morphism X Z h
    let r1 ← match_morphism Z Y g

    match (r1, r2) with
    | (Result.mk g' val_g proof_g, Result.mk h' val_h proof_h) =>
      match Morphism.compose g' h' val_g val_h with
      | Result.mk expr val proof =>
        return {
          expr := expr,
          val  := val,
          proof:= q(by
            rw [<-«$proof», <-«$proof_g», <-«$proof_h»]
          )
        }
  | _ =>
    let idx ← CatM.add_atom f
    return Result.Id f <| Morphism.Nil (Atom.Const X Y f idx)

end


end

def of_eq (_ : (a: R) = c) (_ : b = c) : a = b := by simp only [*]

universe w

def TestEq (α:Q(Type w)) (X Y:Q($α)) : MetaM <| Option Q($X = $Y) := do
  if ← isDefEq X Y then do
    have p : Q($X = $X) := q(by rfl)
    have proof : Q(«$X» = «$Y») := p
    return some proof
  else return none

abbrev EndoHom (C:Type w) (CatC:Category C) (X:C) := @Category.Hom C CatC X X

partial def match_morphism_equality (mvarid:MVarId) : CatM <| List MVarId := do
  let type_eq : Q(Prop) ← mvarid.getType
  match type_eq with
  | ~q($f = $g) => do
    let type_fg ← inferType f
    -- $f and $g are morphism of type $type_f, $type_f have type Type v
    let .sort (.succ v) ← whnf (← inferType type_fg) | throwError "not a type"

    have type_fg : Q(Type v) := type_fg
    have f : Q($type_fg) := f
    have g : Q($type_fg) := g


    match type_fg with
    | ~q(EndoHom $C $CatC $X) =>

      let .sort (.succ u) ← whnf (← inferType C) | throwError "a category shound be a type"

      have f : Q($X ⟶  $X) := f
      have g : Q($X ⟶  $X) := g

      let ⟨f', _, pf⟩ ← @match_morphism_dom_eq_cod u v C CatC X f
      let ⟨g', _, pg⟩ ← @match_morphism_dom_eq_cod u v C CatC X g

      match ← @TestEq v q($X ⟶  $X) f' g' with
      | none => throwError "expressions not equal\n{f}\n{g}\n{f'}\n{g'}"
      | some proof => do
        mvarid.assign <| show Q($f = $g) from q(by
            simp only [«$pg», «$pf», «$proof»]
          )
        return []

    | ~q(@Category.Hom $C $CatC $X $Y) =>

      let .sort (.succ u) ← whnf (← inferType C) | throwError "a category shound be a type"

      have f : Q($X ⟶  $Y) := f
      have g : Q($X ⟶  $Y) := g

      let ⟨f', _, pf⟩ ← @match_morphism u v C CatC X Y f
      let ⟨g', _, pg⟩ ← @match_morphism u v C CatC X Y g

      match ← @TestEq v q($X ⟶  $Y) f' g' with
      | none => throwError "expressions not equal\n{f}\n{g}\n{f'}\n{g'}"
      | some proof => do
        mvarid.assign <| show Q($f = $g) from q(by
            simp only [«$pg», «$pf», «$proof»]
          )
        return []

    | _ => throwError "not a morphism"
  | _ => throwError "not an equality"

elab "reduce_assoc_and_id" : tactic =>
  withMainContext do
    liftMetaTactic fun mvarId => do
      CatM.run (match_morphism_equality mvarId) true


example (C:Type u) [Category C] (X Y:C) (f: X ⟶  Y) (g:X ⟶  X) :
  (f ⊚ 𝟙 X) ⊚ g = 𝟙 Y ⊚ (f ⊚ g) := by reduce_assoc_and_id


end Cat
