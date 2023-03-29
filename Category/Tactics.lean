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
  expr := e
  val  := val
  proof := q(by rfl)

namespace FiniteCat


section

variable {C: Q(Type u)}
variable {CatC: Q(Category.{u, v} $C)}

inductive AtomicMorphism : ∀ X Y: Q($C), Q($X ⟶  $Y) → Type where
| Const : ∀ X Y: Q($C), ∀ f: Q($X ⟶  $Y), Nat → AtomicMorphism X Y f

inductive AtomicMorphismList : ∀ X Y: Q($C), Q($X ⟶  $Y) → Type where
| Nil : ∀ {X Y f}, AtomicMorphism X Y f → AtomicMorphismList X Y f
| Cons: ∀ {X Z: Q($C)} (Y:Q($C)),
  ∀ f: Q($Y ⟶  $Z), ∀ g: Q($X ⟶  $Y),
  AtomicMorphism Y Z f → AtomicMorphismList X Y g → AtomicMorphismList X Z q($f ⊚ $g)
--| RW : ∀ {X Y:Q($C)}, ∀ f g:Q($X ⟶  $Y), Q($f = $g) → AtomicMorphismList X Y f → AtomicMorphismList X Y g


inductive MorphismList : ∀ X Y:Q($C), Q($X ⟶  $Y) → Type where
| Id   : ∀ X: Q($C), MorphismList X X q(𝟙 $X)
| List : ∀ {X Y}, ∀ f, AtomicMorphismList X Y f → MorphismList X Y f


#check Result
#check AtomicMorphismList


def AtomMorphismList.compose {X Y Z: Q($C)} (f1:Q($Y ⟶  $Z)) (f2:Q($X ⟶  $Y))
  (l1:AtomicMorphismList Y Z f1) (l2:AtomicMorphismList X Y f2) :
    @Result _ q($X ⟶  $Z) (@AtomicMorphismList _ _ C CatC X Z) q($f1 ⊚ $f2) :=

  match l1 with
  | AtomicMorphismList.Nil atom => Result.Id q($f1 ⊚ $f2) (.Cons Y f1 f2 atom l2)
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


end

structure Context where
  useTransparancy : Bool

structure State where
  atoms : Array Expr := #[]

abbrev FiniteCatM := ReaderT Context <| StateT State MetaM

def FiniteCatM.run {α:Type} (f:FiniteCatM α) (red:Bool) :
  MetaM α := (f ⟨red⟩).run' {}




end FiniteCat
