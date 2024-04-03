import Std
universe u v w

@[simp] theorem Array.range_size (n:Nat) : (Array.range n).size = n := by
  induction n with
  | zero =>
    simp
  | succ n h =>
    simp [range, Nat.fold, flip]
    simp only [range, flip] at h
    assumption

theorem Array.range_get (n:Nat) (i:Nat) (h1:i<n) :
  have : i < (Array.range n).size := by simp; assumption
  (Array.range n)[i] = i := by
  induction n with
  | zero =>
    cases h1
  | succ n h2 =>
    simp only [range, flip, Nat.fold]
    apply dite (i < n)
    <;> intro h3 <;> simp [h3]
    . rw [get_push_lt]
      simp only [range, flip] at h2
      apply h2 h3
    . have : i = n := by
        simp only [LT.lt, Nat.lt] at h1
        cases h1
        . rfl
        . apply False.elim
          apply h3
          assumption

      induction this
      have := get_push_eq (range i) i
      simp only [range_size] at this
      simp only [range, flip] at this
      assumption


abbrev Vector (t:Type v) (size: Nat) := {t:Array t // t.size = size}

@[simp] theorem Vector.size {t:Type v} {size:Nat} (v:Vector t size) : v.val.size = size :=
  v.property

instance {t:Type v} {size:Nat} : GetElem (Vector t size) Nat t (fun _ i => i < size) where
  getElem v i h :=
    have : i < Array.size v.val := by
      simp only [Vector.size]
      assumption
    v.val[i]


def Vector.set {t:Type v} {size:Nat} (v:Vector t size) (i:Nat) {h:i < size} (elem:t) : Vector t size :=
  have : i < Array.size v.val := by
    simp only [v.property]
    assumption
  ⟨v.val.set ⟨i, by assumption⟩ elem, by simp⟩

theorem Vector.get_set {t:Type v} {size: Nat} (v:Vector t size) (i j:Nat) {hi:i < size} {hj:j < size} (elem:t) :
  (@set t size v i hi elem)[j] = if i = j then elem else v[j] :=
by
  apply Array.get_set

def Vector.range (size:Nat) : Vector Nat size := ⟨Array.range size, by simp⟩

theorem Vector.get_range (size:Nat) (i:Fin size) : (range size)[i] = i := by
  simp [range]
  unfold GetElem.getElem
  unfold instGetElemVectorNatLtInstLTNat
  apply Array.range_get
  exact i.isLt

def Vector.map {α:Type u} {β:Type v} {size:Nat} (f:α → β) (v:Vector α size) : Vector β size := ⟨Array.map f v.val, by simp⟩

@[simp] theorem Vector.map_thm {α:Type u} {β: Type v} {size:Nat} (f:α → β) (v:Vector α size) :
  ∀ i:Fin size, (map f v)[i] = f v[i] := by
  simp [map]
  unfold GetElem.getElem
  unfold instGetElemVectorNatLtInstLTNat
  simp

#check Array.mapIdx
def Vector.mapIdx {α:Type u} {β:Type v} {size:Nat}
  (f:Fin size → α → β) (v:Vector α size) : Vector β size :=
  ⟨Array.mapIdx v.val fun i => by simp only [Vector.size] at i; exact f i, by simp⟩

def Vector.push {α:Type u} {size:Nat} (v:Vector α size) (x:α) : Vector α (.succ size) :=
  ⟨Array.push v.val x, by simp⟩

#check @Array.back_push

#check (fun a:Array Nat => a[0]?)

def Vector.push_last_thm {α:Type u} {size:Nat} (v:Vector α size) (x:α) :
  (v.push x)[size] = x :=
by
  simp only [<-v.property, push]
  unfold GetElem.getElem
  unfold instGetElemVectorNatLtInstLTNat
  simp only
  have := Array.get_push_eq v.val x
  assumption

#check Nat.le_trans

@[simp] def Vector.push_thm {α:Type u} {size:Nat} (v:Vector α size) (x:α) (i:Nat) {hi:i<size} :
  have : i < size+1 := by apply Nat.le_trans hi; simp_arith
  (v.push x)[i] = v[i] :=
by
  simp only [push]
  simp only [<-v.property] at hi
  unfold GetElem.getElem
  unfold instGetElemVectorNatLtInstLTNat
  simp only
  have := Array.get_push_lt v.val x i hi
  assumption

#check Eq.mp

@[simp] theorem Vector.mapIdx_thm {α:Type u} {β:Type v} {size:Nat}
  (f:Fin size → α → β) : ∀ v:Vector α size, ∀ i:Nat, ∀ h:i<size, (mapIdx f v)[i] = f ⟨i, h⟩ v[i] := by
  intro ⟨v, h⟩
  simp [mapIdx]
  unfold GetElem.getElem
  unfold instGetElemVectorNatLtInstLTNat
  intro i iIsLt
  cases h
  simp [Eq.mp]

section


variable {α: Type u} [αSetoid: Setoid α]
variable (size: Nat) (eval: Vector α size) -- (eval: Fin size → α)


structure UnionFind.Data where
  parent: Fin size
  rank: Nat

structure UnionFind where
  tab: Vector (UnionFind.Data size) size
  wf: ∀ i:Fin size, eval[tab[i.val].parent] ≈ eval[i]

namespace UnionFind

instance : Inhabited (UnionFind size eval) where
  default :=
  let f:Fin size → Nat → Data size := fun i _ => ⟨i, 0⟩
  ⟨
    Vector.mapIdx f (Vector.range size),
    by
      intro i
      simp
      apply Setoid.refl
  ⟩


-- set the parent j to the node i
def set_parent (uf:UnionFind size eval) (i j:Fin size) {h:eval[i] ≈ eval[j]} : UnionFind size eval :=
  have iRank := uf.tab[i].rank
  match uf with
  | UnionFind.mk tab wf =>
        {
          tab := tab.set i ⟨j, iRank⟩,
          wf := by
            intro ⟨k, kIsLt⟩
            rw [Vector.get_set tab i k ⟨j, iRank⟩]
            apply dite (i = k)
            <;> intro h1 <;> simp [h1]
            . induction h1
              apply @Setoid.trans _ _ _ (eval[i])
              . apply Setoid.symm
                assumption
              . apply Setoid.refl
            . apply wf ⟨k,kIsLt⟩
            . intros _ i
              intros
              apply i.isLt
        }

-- set the rank r to the node i
def set_rank (uf:UnionFind size eval) (i:Fin size) (r:Nat) : UnionFind size eval :=
  match uf with
  | UnionFind.mk tab wf =>
    let parent := tab[i].parent
    {
      tab := tab.set i ⟨parent, r⟩,
      wf := by
        intro ⟨k, kIsLt⟩
        rw [Vector.get_set tab i k ⟨parent, r⟩]
        apply dite (i = k)
        <;> intro h1 <;> simp [h1]
        . induction h1
          apply @Setoid.trans _ _ _ eval[i]
          . apply wf i
          . apply Setoid.refl
        . apply wf ⟨k, kIsLt⟩
        . intro _ i
          intros
          apply i.isLt
    }

instance {i:Fin size} : Inhabited {j:Fin size // eval[i] ≈ eval[j]} where
  default := ⟨i, Setoid.refl eval[i]⟩

partial def find (uf:UnionFind size eval) (i:Fin size) : (UnionFind size eval × {j:Fin size // eval[i] ≈ eval[j]}) :=
  if uf.tab[i].parent = i then
    (uf, ⟨i, Setoid.refl eval[i]⟩)
  else
    let (new_uf, r) := find uf uf.tab[i].parent
    let out : {j:Fin size // eval[i] ≈ eval[j]} := ⟨
        r.val,
        by
          apply @Setoid.trans _ _ eval[i] eval[uf.tab[i].parent] eval[r.val]
          . apply Setoid.symm
            apply uf.wf i
          . apply r.property
      ⟩

    ⟨@set_parent α _ size eval new_uf i out.val out.property, out⟩

partial def union (uf:UnionFind size eval) (i j:Fin size) {h:eval[i] ≈ eval[j]} : UnionFind size eval :=
  let (uf, iRoot) := find size eval uf i
  let (uf, jRoot) := find size eval uf j

  have : iRoot < size := iRoot.val.isLt
  have : jRoot < size := jRoot.val.isLt
  have h : eval[iRoot.val] ≈ eval[jRoot.val] := by
    apply Setoid.trans (Setoid.symm iRoot.property)
    apply Setoid.trans h
    exact jRoot.property

  let iRank := uf.tab[iRoot.val].rank
  let jRank := uf.tab[jRoot.val].rank

  if iRoot.val ≠ jRoot.val then
    if iRank < jRank then
      @set_parent _ _ size eval uf iRoot jRoot h
    else
      let uf := @set_parent _ _ size eval uf jRoot iRoot (Setoid.symm h)
      if iRank = jRank then
        set_rank size eval uf iRoot (iRank + 1)
      else
        uf
  else
    uf

end UnionFind


-- vector ef elements equivalent of eval
structure ResultVector (E:α → Type) where
  vec: Vector (Σ x:α, E x) size
  wf : ∀ i:Fin size, vec[i].fst ≈ eval[i]

namespace ResVector

variable (E:α → Type)

structure Partial (E: α → Type) (s:Nat) where
  h : s ≤ size
  vec: Vector (Σ x:α, E x) s
  wf : ∀ i:Fin s, vec[i].fst ≈ eval[i]

#check Vector.push_last_thm

def from_monad_fun {m:Type u → Type w} [Monad m] (f:(x:α) → m {p:Σ y:α, E y // p.fst ≈ x}) : m <| ResultVector size eval E :=
  let rec aux (s:Nat) {h:s ≤ size} : m <| Partial size eval E s :=
    match s with
    | 0 =>
      pure ⟨by assumption, ⟨#[], by simp_arith⟩, by intro i; cases i.isLt⟩
    | s + 1 => do
      let x ← f eval[s]
      let p ← @aux s (by apply Nat.le_trans _ h; simp_arith only)
      pure ⟨by assumption, p.vec.push x.val, fun i =>
        if h: i.val < s then by
          have : ∀ (i:Fin (s+1)), ∀ (h:i<s), (p.vec.push x.val)[i] = p.vec[i]
            := fun i h => @Vector.push_thm _ _ p.vec x.val i.val h
          rw [this i h]
          apply p.wf ⟨i, h⟩
        else by
          have : s = i := by
            have := i.isLt
            simp_arith only [*] at h this
            apply Nat.le_antisymm h this

          simp only [←this, getElem_fin]
          rw  [Vector.push_last_thm p.vec x.val]
          apply x.property
      ⟩


  @aux size (by simp_arith only) >>=
    fun p => by
      exact pure ⟨p.vec, p.wf⟩

end ResVector


section

class CompSetoid (α:Type u) [Setoid α] where
  comp: α → α → α
  wf: ∀ a b c d:α, a ≈ c → b ≈ d → comp a b ≈ comp c d


variable [αCompSetoid:CompSetoid α]

-- type of input: a list of equality of list of term
structure State where
  vec: Vector (Option (Fin size × Fin size)) size
  wf: ∀ i j k:Fin size, vec[i] = some (j, k) → eval[i] ≈ αCompSetoid.comp eval[j] eval[k]

  -- occ[i] contain all the indices j with i ∈ vec[j]
  occ: Vector (List (Fin size)) size

structure Input where
  vec: Vector (Option (Fin size × Fin size)) size
  wf: ∀ i j k:Fin size, vec[i] = some (j, k) → eval[i] ≈ αCompSetoid.comp eval[j] eval[k]
  equals: List {p:Fin size × Fin size // eval[p.1] ≈ eval[p.2]}

#check Id
def State.compute_occ (state:State size eval) : State size eval := Id.run do
  let mut state := state
  for h:i in [0:size] do
      have i_lt_size : i < size := h.2
      if let some (j, k) ← state.vec[i] then
        if j.val ≠ i then
          state := {state with occ := @Vector.set _ _ state.occ j j.isLt <| ⟨i, i_lt_size⟩ :: state.occ[j]}

        if k.val ≠ i ∧ k.val ≠ j then
          state := {state with occ := @Vector.set _ _ state.occ k k.isLt <| ⟨i, i_lt_size⟩ :: state.occ[k]}
  return state

#check UnionFind.find

abbrev M (β:Type) := ReaderT (State size eval) (StateM (UnionFind size eval)) β

partial def M.Find (i:Fin size) : M size eval {j:Fin size // eval[i] ≈ eval[j]} :=
  modifyGet fun uf =>
    let (uf, out) := UnionFind.find size eval uf i
    (out, uf)

partial def M.Union (i j:Fin size) {h:eval[i] ≈ eval[j]} : M size eval Unit :=
  modify fun uf => @UnionFind.union α αSetoid size eval uf i j h

inductive OptionP (P:Prop) where
| noneP : OptionP P
| someP : P → OptionP P
instance {P:Prop} : Inhabited (OptionP P) where
  default := .noneP


def M.FindCongruent (i j:Fin size) : M size eval (OptionP (eval[i] ≈ eval[j])) := do
  let ⟨iR, iH⟩ ← Find size eval i
  let ⟨jR, jH⟩ ← Find size eval j
  if h:iR = jR then
    return .someP (by
      simp only [h] at *
      apply Setoid.trans iH
      exact Setoid.symm jH
    )
  else
    return .noneP

def M.Congruent (i j:Fin size) : M size eval (OptionP (eval[i] ≈ eval[j])) := do
  match ←FindCongruent size eval i j with
  | .someP h => return .someP h
  | .noneP => do
    let ⟨vec, wf, _⟩ ← read
    match h:(vec[i], vec[j]) with
    | (some (a, b), some (c, d)) => do
      match (←FindCongruent size eval a c, ←FindCongruent size eval b d) with
      | (.someP hi, .someP hj) => return .someP (by
          have wfi := wf i a b
          have wfj := wf j c d
          generalize vec[i] = x at *
          generalize vec[j] = y at *
          cases h
          apply Setoid.trans (wfi (Eq.refl _))
          apply Setoid.trans _ (Setoid.symm (wfj (Eq.refl _)))
          exact CompSetoid.wf _ _ _ _ hi hj
        )
      | _ => return .noneP
    | _ => return .noneP

def M.Congruent' (i j:Fin size) : M size eval (OptionP (eval[i] ≈ eval[j])) := do
  for hx:x in [0:size] do
    for hy:y in [0:size] do
      if let .someP h1 ← Congruent size eval ⟨x, hx.2⟩ i then do
        if let .someP h2 ← Congruent size eval ⟨y, hy.2⟩ j then do
          if let .someP h3 ← Congruent size eval ⟨x, hx.2⟩ ⟨y, hy.2⟩ then do
            return .someP (by
              apply Setoid.trans _ h2
              apply Setoid.trans _ h3
              apply Setoid.symm
              exact h1
            )
  return .noneP

-- check if i j are congruent, if yes, merge i and j and propagate
partial def M.TryMerge (i j:Fin size) : M size eval (OptionP (eval[i] ≈ eval[j])) := do
  -- if i and j are findCongruent: stop
  match ←FindCongruent size eval i j with
  | .someP h => return .someP h
  | .noneP => do
    match ←Congruent' size eval i j with
    | .noneP => return .noneP
    | .someP h => do
      @Union _ _ size eval _ i j h
      for hx:x in [0:size] do
        for hy:y in [0:size] do
          let _ ← TryMerge ⟨x, hx.2⟩ ⟨y, hy.2⟩
      /-
      let ⟨_, _, occ⟩ ← read
      have occ_i := occ[i]
      have occ_j := occ[j]
      for x in occ_i do
        for y in occ_j do
          let _ ← TryMerge x y
        let _ ← TryMerge x j
      for y in occ_j do
        let _ ← TryMerge i y
      -/
      return .someP h


partial def M.Merge (i j:Fin size) {h:eval[i] ≈ eval[j]} : M size eval Unit := do
  -- if i and j are findCongruent: stop
  match ←FindCongruent size eval i j with
  | .someP _ => return ()
  | .noneP => do
    @Union _ _ size eval _ i j h
    for hx:x in [0:size] do
      for hy:y in [0:size] do
        let _ ← TryMerge size eval ⟨x, hx.2⟩ ⟨y, hy.2⟩
    /-
    let ⟨_, _, occ⟩ ← read
    have occ_i := occ[i]
    have occ_j := occ[j]
    for x in occ_i do
      for y in occ_j do
        let _ ← TryMerge size eval x y
      let _ ← TryMerge size eval x j
    for y in occ_j do
      let _ ← TryMerge size eval i y
    -/

#check ReaderT.run
#check StateT.run
#check Id.run
-- evaluate an input and return an UnionFind

partial def M.run' (l:List {p:Fin size × Fin size // eval[p.1] ≈ eval[p.2]}) : M size eval Unit := do
  for ⟨⟨i, j⟩, h⟩ in l do
    have : eval[i] ≈ eval[j] := by simp only at h; assumption
    @Merge _ _ size eval _ i j this

partial def M.run (input:Input size eval) : UnionFind size eval :=
  match input with
  | Input.mk vec wf equals =>
    Id.run do
      let (_, out) ← StateT.run
        (ReaderT.run (run' size eval equals)
          ⟨vec, wf, Vector.map (fun _ => []) (Vector.range size)⟩
        ) default
      out

end

end

namespace Test

def TestFun := Int → Int

instance : Setoid TestFun where
  r := Eq
  iseqv := by
    apply Equivalence.mk
    case refl =>
      intro x
      rfl
    case trans =>
      apply Eq.trans
    case symm =>
      apply Eq.symm

instance : CompSetoid TestFun where
  comp
  | f, g => fun x => f (g x)

  wf := by
    intro a b c d h1 h2
    simp [HasEquiv.Equiv, Setoid.r] at *
    induction h1
    induction h2
    rfl

def f:TestFun := fun x => x
def g:TestFun := fun x => x
def h:TestFun := fun x => x
def ident:TestFun := fun x => x

open CompSetoid(comp)

-- def compL : TestFun → List TestFun → TestFun
-- | f, x :: xs => comp f (compL x xs)
-- | f, [] => f
--
-- def size := 7
-- def eval: Vector TestFun size := ⟨#[
--   g,
--   f,
--   comp f g,
--   compL f [f, g],
--   compL f [f, f, g],
--   compL f [f, f, f, g],
--   compL f [f, f, f, f, g]
--   ], by simp⟩
--
-- def input: Input size eval where
--   vec := ⟨
--     #[
--       none,
--       none,
--       some (⟨1, by simp⟩, ⟨0, by simp⟩),
--       some (⟨1, by simp⟩, ⟨2, by simp⟩),
--       some (⟨1, by simp⟩, ⟨3, by simp⟩),
--       some (⟨1, by simp⟩, ⟨4, by simp⟩),
--       some (⟨1, by simp⟩, ⟨5, by simp⟩)
--     ]
--     , by simp
--   ⟩
--
--   wf := sorry
--
--   equals := [
--     ⟨(⟨0, by simp⟩, ⟨3, by simp⟩), by sorry⟩,
--     ⟨(⟨0, by simp⟩, ⟨6, by simp⟩), by sorry⟩
--   ]
--
-- #eval (UnionFind.find size eval (M.run size eval input) ⟨1, by simp⟩).2.val
-- #eval (UnionFind.find size eval (M.run size eval input) ⟨2, by simp⟩).2.val
--
def size := 12
def eval: Vector TestFun size := ⟨#[
  ident, f, g, h,
  comp f g,
  comp h f,
  comp ident f, comp f ident,
  comp ident g, comp g ident,
  comp ident h, comp h ident
], by simp⟩

def input: Input size eval where
  vec := ⟨
    #[
      none,
      none,
      none,
      none,
      some (⟨1, by simp⟩, ⟨2, by simp⟩),
      some (⟨3, by simp⟩, ⟨1, by simp⟩),
      some (⟨0, by simp⟩, ⟨1, by simp⟩),
      some (⟨1, by simp⟩, ⟨0, by simp⟩),
      some (⟨0, by simp⟩, ⟨2, by simp⟩),
      some (⟨2, by simp⟩, ⟨0, by simp⟩),
      some (⟨0, by simp⟩, ⟨3, by simp⟩),
      some (⟨3, by simp⟩, ⟨0, by simp⟩)
    ]
    , by simp
  ⟩

  wf := sorry
  equals := [
    ⟨(⟨0, by simp⟩, ⟨4, by simp⟩), by sorry⟩,
    ⟨(⟨0, by simp⟩, ⟨5, by simp⟩), by sorry⟩,

    ⟨(⟨1, by simp⟩, ⟨6, by simp⟩), by sorry⟩,
    ⟨(⟨1, by simp⟩, ⟨7, by simp⟩), by sorry⟩,
    ⟨(⟨2, by simp⟩, ⟨8, by simp⟩), by sorry⟩,
    ⟨(⟨2, by simp⟩, ⟨9, by simp⟩), by sorry⟩,
    ⟨(⟨3, by simp⟩, ⟨10, by simp⟩), by sorry⟩,
    ⟨(⟨3, by simp⟩, ⟨11, by simp⟩), by sorry⟩
  ]

#eval (UnionFind.find size eval (M.run size eval input) ⟨2, by simp⟩).2.val
#eval (UnionFind.find size eval (M.run size eval input) ⟨3, by simp⟩).2.val
end Test
