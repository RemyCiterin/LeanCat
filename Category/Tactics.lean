import Qq

import Lean

import Category.Basic

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

namespace Cat

structure Context where
  useTransparancy : Bool

structure State where
  atoms : Array Expr := #[]

instance : Inhabited State where
  default := ⟨#[]⟩

abbrev CatM := ReaderT Context <| StateT State MetaM

def CatM.run {α:Type} (f:CatM α) (red:Bool) :
  MetaM α := (f ⟨red⟩).run' {}

def CatM.add_atom (e:Expr) : CatM Nat := do
  let table ← get
  if (← read).useTransparancy then
    for h : i in [0:table.atoms.size] do
      have : i < table.atoms.size := h.2
      if ← isDefEq e table.atoms[i] then
        return i
  modifyGet fun c => (table.atoms.size, {c with atoms := c.atoms.push e})

section

variable {C: Q(Type u)}
variable {CatC: Q(Category.{u, v} $C)}

inductive Atom : ∀ X Y: Q($C), Q($X ⟶  $Y) → Type where
| Const : ∀ X Y: Q($C), ∀ f: Q($X ⟶  $Y), Nat → Atom X Y f

inductive AtomicMorphism : ∀ X Y: Q($C), Q($X ⟶  $Y) → Type where
| Nil : ∀ {X Y f}, Atom X Y f → AtomicMorphism X Y f
| Cons: ∀ {X Z: Q($C)} (Y:Q($C)),
  ∀ f: Q($Y ⟶  $Z), ∀ g: Q($X ⟶  $Y),
  Atom Y Z f → AtomicMorphism X Y g → AtomicMorphism X Z q($f ⊚ $g)


inductive Morphism : ∀ X Y:Q($C), Q($X ⟶  $Y) → Type where
| Id   : ∀ X: Q($C), Morphism X X q(𝟙 $X)
| List : ∀ {X Y}, ∀ f, AtomicMorphism X Y f → Morphism X Y f

#check Result
#check AtomicMorphism


def AtomicMorphism.compose {X Y Z: Q($C)} (f1:Q($Y ⟶  $Z)) (f2:Q($X ⟶  $Y))
  (l1:AtomicMorphism Y Z f1) (l2:AtomicMorphism X Y f2) :
    @Result _ q($X ⟶  $Z) (@AtomicMorphism _ _ C CatC X Z) q($f1 ⊚ $f2) :=

  match l1 with
  | AtomicMorphism.Nil atom => Result.Id q($f1 ⊚ $f2) (.Cons Y f1 f2 atom l2)
  | .Cons Z f1 g1 atom l1 =>
  by
    let r := compose g1 f2 l1 l2
    generalize h: r.expr = expr
    have proof : Q($g1 ⊚ $f2 = $expr) := r.proof
    exact {
      expr := q($f1 ⊚ $r.expr),
      val  := .Cons Z f1 q($r.expr) atom r.val,
      proof:= show Q($f1 ⊚ $expr = ($f1 ⊚ $g1) ⊚ $f2) from q(by
        simp
        have : $g1 ⊚ $f2 = $expr := $proof
        rw [this]
      )
    }


def Morphism.compose {X Y Z: Q($C)} (f1: Q($Y ⟶  $Z)) (f2: Q($X ⟶  $Y))
  (l1: @Morphism _ _ C CatC Y Z f1) (l2: @Morphism _ _ C CatC X Y f2) :
  @Result _ q($X ⟶  $Z) (@Morphism _ _ C CatC X Z) q($f1 ⊚ $f2) :=
by
  cases l1 with
  | Id =>
    apply Result.mk
    case expr =>
      exact f2
    case val =>
      exact l2
    case proof =>
      exact q(by
        rw [Category.id_comp]
      )
  | List _ a =>
    cases l2 with
    | Id =>
      apply Result.mk
      case expr =>
        exact f1
      case val =>
        exact (.List _ a)
      case proof =>
        exact q(by
          rw [Category.comp_id]
        )
    | List _ b =>
      apply Result.map (AtomicMorphism.compose f1 f2 a b)
      apply Morphism.List


end
end Cat
