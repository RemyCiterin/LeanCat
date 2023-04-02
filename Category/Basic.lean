universe u v

/- *** definition of category *** -/

class Category (C: Type u) where
  Hom : C → C → Type v

  id : ∀ X: C, Hom X X

  comp : ∀ {X Y Z: C}, Hom Y Z → Hom X Y → Hom X Z

  comp_id : ∀ {X Y:C}, ∀ f: Hom X Y, comp f (id X) = f
  id_comp : ∀ {X Y:C}, ∀ f: Hom X Y, comp (id Y) f = f

  assoc : ∀ {W X Y Z: C}, ∀ f:Hom Y Z, ∀ g: Hom X Y, ∀ h:Hom W X, comp (comp f g) h = comp f (comp g h)

infixr:10 " ⟶  " => Category.Hom
infixr:80 " ⊚ " => Category.comp
notation "𝟙" => Category.id

open Category in
#check ∀ (C:Type u) [Category C] (W X Y Z: C), ∀ f:Y ⟶  Z, ∀ g: X ⟶  Y, ∀ h:W ⟶  X, (f ⊚ g) ⊚ h = f ⊚ (g ⊚ h)

namespace Category

@[simp] instance : Category (Type u) where
  Hom X Y := X → Y

  id X := fun x:X => x

  comp f g := f ∘ g

  comp_id := by intros; simp only [Function.comp]
  id_comp := by intros; simp only [Function.comp]
  assoc := by intros; simp only [Function.comp]

-- theorems for simp tactic
@[simp] theorem comp_id_thm {C:Type u} [Category C] {X Y:C} (f:X ⟶  Y) : f ⊚ 𝟙 X = f := comp_id f
@[simp] theorem id_comp_thm {C:Type u} [Category C] {X Y:C} (f:X ⟶  Y) : 𝟙 Y ⊚ f = f := id_comp f

@[simp] theorem assoc_thm {C:Type u} [Category C] {W X Y Z:C} (f:Y ⟶  Z) (g:X ⟶  Y) (h:W ⟶  X) :
  (f ⊚ g) ⊚ h = f ⊚ g ⊚ h := assoc _ _ _


/- *** definition of oposite category *** -/
def Op (C:Type u) [Category C] : Type u := C

@[simp] instance {C:Type u} [Category C] : Category (Category.Op C) where
  Hom X Y := @Category.Hom C _ Y X

  id X := @Category.id C _ X

  comp f g := @Category.comp C _ _ _ _ g f

  comp_id := by simp
  id_comp := by simp
  assoc := by simp

/-  *** definition of functor ***  -/



structure Functor (C:Type u) (D:Type v) [Category C] [Category D] where
  F : C → D

  Fmap : {X Y:C} → (f:X ⟶  Y) → ((F X) ⟶  (F Y))

  Fmap_id : {X: C} → Fmap (𝟙 X) = 𝟙 (F X)

  Fmap_comp : {X Y Z: C} → (f:Y ⟶  Z) → (g:X ⟶  Y) → Fmap (f ⊚ g) = Fmap f ⊚ Fmap g

infixr:26 " ⥤ " => Category.Functor

#check Functor.Fmap

syntax:90 term:90 " << " term:70 " >> " : term
macro_rules
  | `($F:term << $f:term >>) => `(Category.Functor.Fmap $F $f)

namespace Functor

variable {C:Type u} {D:Type v} [Category C] [Category D]
variable (F: C ⥤ D)

-- theorems for simp tactic
@[simp] theorem Fmap_id_thm {X:C} : F<<𝟙 X>> = 𝟙 (F.F X) := F.Fmap_id
@[simp] theorem Fmap_comp_thm {X Y Z:C} (f:Y ⟶  Z) (g:X ⟶  Y) : F<<f ⊚ g>> = F<<f>> ⊚ F<<g>> := F.Fmap_comp f g

-- covariant representation of an object c:C
def CovRepr {C:Type u} [Category.{u, v} C] (c:C) : C ⥤ Type v :=
  {
    F := fun X:C => c ⟶  X,
    Fmap := fun {X Y: C} (f: X ⟶  Y) (g:c ⟶  X) => f ⊚ g,
    Fmap_id := by intros; simp,
    Fmap_comp := by simp [Function.comp]
  }


def ContraRepr {C:Type u} [Category.{u, v} C] := @CovRepr (Op C) _

instance {C:Type u} {D:Type v} [Category C] [Category D] : Coe (Functor C D) (C → D) :=
  ⟨Functor.F⟩

end Functor


/- *** definition of over and under category *** -/

def Over (C:Type u) [Category C] (c:C) := Σ x:C, x ⟶  c

def Under (C:Type u) [Category C] := Over (Op C)


instance {C:Type u} [Category C] {c:C} : Category (Over C c) where
  Hom X Y := {f: X.fst ⟶  Y.fst // Y.snd ⊚ f = X.snd}

  id X := ⟨𝟙 X.fst, by simp only [comp_id]⟩

  comp f g := ⟨f.val ⊚ g.val, by simp [<-assoc, f.property, g.property]⟩

  comp_id := by intros; simp only [comp_id]
  id_comp := by intros; simp only [id_comp]
  assoc := by intros; simp only [assoc]


instance {C:Type u} [Category C] {c:C} : Category (Under C c) :=
  inferInstanceAs (Category (Over (Op C) c))

/- *** definition of isomorphism *** -/

structure Iso {C: Type u} [Category C] (X Y: C) where
  hom : X ⟶  Y
  inv : Y ⟶  X

  hom_inv : hom ⊚ inv = 𝟙 Y
  inv_hom : inv ⊚ hom = 𝟙 X


theorem IsoSymm {C:Type u} [Category C] (X Y: C) (h:Iso X Y) : Iso Y X :=
  {hom := h.inv, inv := h.hom, hom_inv := h.inv_hom, inv_hom := h.hom_inv}

def IsoFunctor {C:Type u} {D:Type v} [Category C] [Category D] (F: C ⥤ D)
  (X Y:C) (iso: Iso X Y) : Iso (F.F X) (F.F Y) :=
  {
    hom := F<<iso.hom>>,
    inv := F<<iso.inv>>,
    inv_hom := by rw [<-Functor.Fmap_comp_thm, iso.inv_hom, Functor.Fmap_id],
    hom_inv := by rw [<-Functor.Fmap_comp_thm, iso.hom_inv, Functor.Fmap_id]
  }

infixr:10 " ≅ " => Category.Iso

/- *** definition of monomorphism and epimorphism *** -/

def Monomorphism {C:Type u} [Category C] {X Y:C} (f:X ⟶  Y) : Prop :=
  ∀ W:C, ∀ h k: W ⟶  X, f ⊚ h = f ⊚ k → h = k

def Epimorphism {C:Type u} [Category C] {X Y:C} (f:X ⟶  Y) : Prop :=
  ∀ Z:C, ∀ h k: Y ⟶  Z, h ⊚ f = k ⊚ f → h = k

theorem EpiMonoFromProd {C:Type u} [Category C] {X Y:C} (f:X ⟶  Y) (g:Y ⟶  X) :
  f ⊚ g = 𝟙 Y → Epimorphism f ∧ Monomorphism g :=
by
  intro h1
  constructor
  . intro Z h k h2
    have h3 : (h ⊚ f) ⊚ g = (k ⊚ f) ⊚ g := by
      rw [h2]
    simp [h1] at h3
    assumption
  . intro W h k h2
    have h3 : (f ⊚ g) ⊚ h = (f ⊚ g) ⊚ k := by
      rw [assoc, assoc, h2]
    rw [h1, id_comp, id_comp] at h3
    assumption

theorem IsoHomEq
  {C:Type u} [Category C]
  {X Y: C} (i1 i2: X ≅ Y) (h1:i1.hom = i2.hom) :
  i1 = i2 :=
by
  suffices i1.inv = i2.inv by
    cases i1
    cases i2
    cases this
    cases h1
    simp only
  calc
    i1.inv = i1.inv ⊚ (i2.hom ⊚ i2.inv) := by rw [i2.hom_inv, comp_id]
    _      = (i1.inv ⊚ i2.hom) ⊚ i2.inv := by rw [<-assoc]
    _      = (i1.inv ⊚ i1.hom) ⊚ i2.inv := by rw [h1]
    _      = i2.inv                     := by rw [i1.inv_hom, id_comp]

/- *** definition of natural transformation and isomorphism *** -/

section

variable {C:Type u} {D:Type v} [Category C] [Category D]

structure NatTrans
  (F G: C ⥤ D) where

  map : ∀ X:C, F.F X ⟶  G.F X

  comp : (X Y: C) → (f:X ⟶  Y) → G<<f>> ⊚ map X = map Y ⊚ F<<f>>

@[simp] theorem NatTrans.eqMap (F G: C ⥤ D) : ∀ t1 t2: NatTrans F G, t1.map = t2.map ↔ t1 = t2 := by
  intro ⟨m1, c1⟩ ⟨m2, c2⟩
  constructor <;> intro h
  case mp =>
    cases h
    simp only
  case mpr =>
    cases h
    simp only

def NatTrans.id (F:C ⥤ D) : NatTrans F F where
  map X := 𝟙 (F.F X)

  comp := by simp

def NatTrans.vcomp
  (F G H:C ⥤ D) (T1:NatTrans G H) (T2:NatTrans F G) : NatTrans F H :=
  {
    map := fun X:C => T1.map X ⊚ T2.map X,
    comp := by
      intro X Y f
      simp only
      calc
        H<<f>> ⊚ map T1 X ⊚ map T2 X = (H<<f>> ⊚ map T1 X) ⊚ map T2 X := by rw [<-assoc]
        _ = (map T1 Y ⊚ G<<f>>) ⊚ map T2 X := by rw [T1.comp X Y]
        _ = map T1 Y ⊚ (map T2 Y ⊚ F<<f>>) := by rw [assoc, T2.comp X Y]
      rw [assoc]
  }


/- *** definition of functor category *** -/

instance : Category (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F

  comp T₁ T₂ := NatTrans.vcomp _ _ _ T₁ T₂

  comp_id := by
    intros; simp only [NatTrans.id, NatTrans.vcomp, comp_id]

  id_comp := by
    intros; simp only [NatTrans.id, NatTrans.vcomp, id_comp]

  assoc := by
    intros; simp only [NatTrans.id, NatTrans.vcomp, assoc]

def NatIso (F G: C ⥤ D) := F ≅ G

#check Functor.CovRepr


end

/- *** definition of a representable fonctor *** -/
def Representable {C:Type u} [Category.{u, v} C] (F: C ⥤ Type v) := Σ c:C, Functor.CovRepr c ≅ F


/- *** definition of constant functor *** -/
def Functor.Constant (C:Type u) [Category C] : C ⥤ Type v where
  F _ := PUnit

  Fmap _ := fun u:PUnit => u

  Fmap_id := by
    simp

  Fmap_comp := by
    simp


def Initial (C:Type u) [Category C] := Representable <| Functor.Constant C

namespace Initial
variable {C:Type u} [Category.{u, v} C] (I:Initial C)

#print Functor.CovRepr

def getObj : C := I.fst

def getMorphism (X:C) : I.fst ⟶  X := I.snd.inv.map X PUnit.unit

def uniqueness (X:C) (f g:I.fst ⟶  X) : f = g := by
  let a := Functor.Constant C <<f>> ⊚ I.snd.hom.map I.fst
  let b := Functor.Constant C <<g>> ⊚ I.snd.hom.map I.fst
  let c := I.snd.hom.map X ⊚ Functor.CovRepr I.fst <<f>>
  let d := I.snd.hom.map X ⊚ Functor.CovRepr I.fst <<g>>

  have h1 : c = a := by
    have := I.snd.hom.comp I.fst X f
    simp only [<-this]
  have h2 : d = b := by
    have := I.snd.hom.comp I.fst X g
    simp only [<-this]

  have : Functor.CovRepr I.fst <<f>> = Functor.CovRepr I.fst <<g>> := by
    calc
      Functor.CovRepr I.fst <<f>> = (I.snd.inv ⊚ I.snd.hom).map X ⊚ Functor.CovRepr I.fst <<f>>
        := by rw [I.snd.inv_hom]; simp only [Category.id, NatTrans.id, Function.comp, Category.comp]
      _ = (I.snd.inv.map X ⊚ I.snd.hom.map X) ⊚ Functor.CovRepr I.fst <<f>>
        := by simp only [Category.comp, NatTrans.vcomp]
      _ = I.snd.inv.map X ⊚ a
        := by rw [assoc, <-h1]
      _ = I.snd.inv.map X ⊚ b
        := by simp only [Functor.Constant]
      _ = (I.snd.inv.map X ⊚ I.snd.hom.map X) ⊚ Functor.CovRepr I.fst <<g>>
        := by rw [<-h2, <-assoc]
      _ = (I.snd.inv ⊚ I.snd.hom).map X ⊚ Functor.CovRepr I.fst <<g>>
        := by simp only [Category.comp, NatTrans.vcomp]
      _ = Functor.CovRepr I.fst <<g>>
        := by rw [I.snd.inv_hom]; simp only [Category.id, NatTrans.id, Function.comp, Category.comp]

  have : Functor.Fmap (Functor.CovRepr I.fst) f (𝟙 I.fst) = Functor.Fmap (Functor.CovRepr I.fst) g (𝟙 I.fst) := by
    rw [this]
  simp only [Functor.CovRepr, comp_id_thm] at this
  assumption


end Initial

def Terminal (C:Type u) [Category C] := Initial (Op C)

end Category
