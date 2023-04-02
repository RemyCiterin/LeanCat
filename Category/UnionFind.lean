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


namespace UnionFind

variable {α: Type u} [αSetoid: Setoid α]
variable (size: Nat) (eval: Fin size → α)


structure Data where
  parent: Fin size
  rank: Nat


structure UnionFind where
  tab: Vector (Data size) size
  wf: ∀ i:Fin size, eval tab[i.val].parent ≈ eval i

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

instance {i:Fin size} : Inhabited {j:Fin size // eval i ≈ eval j} where
  default := ⟨i, Setoid.refl (eval i)⟩

partial def find (uf:UnionFind size eval) (i:Fin size) : {j:Fin size // eval i ≈ eval j} :=
  if uf.tab[i].parent = i then
    ⟨i, Setoid.refl (eval i)⟩
  else
    let r := @find  uf uf.tab[i].parent
    ⟨
      r.val,
      by
        apply @Setoid.trans _ _ (eval i) (eval uf.tab[i].parent) (eval r.val)
        . apply Setoid.symm
          apply uf.wf i
        . apply r.property
    ⟩

-- set the parent j to the node i
def set_parent (uf:UnionFind size eval) (i j:Fin size) {h:eval i ≈ eval j} : UnionFind size eval :=
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
              apply @Setoid.trans _ _ _ (eval i)
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
          apply @Setoid.trans _ _ _ (eval i)
          . apply wf i
          . apply Setoid.refl
        . apply wf ⟨k, kIsLt⟩
        . intro _ i
          intros
          apply i.isLt
    }


partial def union (uf:UnionFind size eval) (i j:Fin size) {h:eval i ≈ eval j} : UnionFind size eval :=
  let iRoot := find size eval uf i
  let jRoot := find size eval uf j

  have h : eval iRoot ≈ eval jRoot := by
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

