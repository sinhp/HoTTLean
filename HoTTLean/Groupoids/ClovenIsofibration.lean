import Mathlib.CategoryTheory.FiberedCategory.HomLift
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import HoTTLean.Grothendieck.Groupoidal.IsPullback
import HoTTLean.Grothendieck.Groupoidal.Basic
import HoTTLean.Groupoids.Pi

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section

namespace CategoryTheory

namespace Functor

namespace Fiber
section

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]
variable {p : 𝒳 ⥤ 𝒮} {S : 𝒮}

@[simp]
lemma functor_obj_fiberInclusion_obj (a : Fiber p S) :
    p.obj (Fiber.fiberInclusion.obj a) = S :=
  a.2

lemma functor_map_fiberInclusion_map {a b : Fiber p S}
    (f : a ⟶ b) :
    p.map (Fiber.fiberInclusion.map f) = eqToHom (by simp) := by
  simp [IsHomLift.fac' p (𝟙 S) (Fiber.fiberInclusion.map f)]

lemma hext {S'} (hS : S' ≍ S) {a : Fiber p S}
    {a' : Fiber p S'} (h : Fiber.fiberInclusion.obj a ≍ Fiber.fiberInclusion.obj a') : a ≍ a' := by
  subst hS
  exact heq_of_eq (Subtype.ext h.eq)

lemma hom_hext {S'} (hS : S' ≍ S) {a b : Fiber p S}
    {a' b' : Fiber p S'} (ha : a ≍ a') (hb : b ≍ b') {φ : a ⟶ b}
    {ψ : a' ⟶ b'} (h : Fiber.fiberInclusion.map φ ≍ Fiber.fiberInclusion.map ψ) : φ ≍ ψ := by
  aesop_cat

end

variable {Γ : Type u} {E : Type u} [Groupoid.{v} Γ] [Groupoid.{v} E] {F : E ⥤ Γ}

instance {X : Γ} : IsGroupoid (F.Fiber X) where
  all_isIso f := {
    out :=
    have := f.2
    ⟨Fiber.homMk F _ (CategoryTheory.inv f.1), by
      apply Subtype.ext
      change f.1 ≫ CategoryTheory.inv f.1 = 𝟙 _
      simp, by
      apply Subtype.ext
      change CategoryTheory.inv f.1 ≫ f.1 = 𝟙 _
      simp⟩ }

instance {X : Γ} : Groupoid (F.Fiber X) := Groupoid.ofIsGroupoid

end Fiber

section

structure ClovenIsofibration {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]
    (F : C ⥤ D) where
  liftObj {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) : C
  liftIso {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) : X' ⟶ liftObj f hX'
  isHomLift {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) :
    F.IsHomLift f (liftIso f hX')
  liftIso_IsIso {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) :
   IsIso (liftIso f hX')

namespace ClovenIsofibration

section

variable {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D] {F : C ⥤ D}
  (I : ClovenIsofibration F)

instance {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) :
  F.IsHomLift f (I.liftIso f hX') := I.isHomLift f hX'

instance {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X):
  IsIso (ClovenIsofibration.liftIso I f hX') := ClovenIsofibration.liftIso_IsIso I f hX'

@[simp]
lemma obj_liftObj {X Y : D} (f : X ⟶ Y) [IsIso f]
    {X' : C} (hX' : F.obj X' = X) : F.obj (I.liftObj f hX') = Y :=
  IsHomLift.codomain_eq F f (I.liftIso f hX')

lemma map_liftIso {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C}
    (hX' : F.obj X' = X) :
  eqToHom hX'.symm ≫ F.map (I.liftIso f hX') ≫ eqToHom (obj_liftObj ..) = f := by
  have i : F.IsHomLift f (I.liftIso f hX') := I.isHomLift ..
  symm
  apply IsHomLift.fac

lemma map_liftIso' {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C}
    (hX' : F.obj X' = X) : F.map (I.liftIso f hX') =
    eqToHom hX' ≫ f ≫ eqToHom (by simp[obj_liftObj]) := by
    simp[← map_liftIso I f hX']

@[simp]
lemma liftObj_comp_aux {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C}
    (hX' : F.obj X' = X) (Y' : C) (hY' : I.liftObj f hX' = Y') : F.obj Y' = Y := by
  subst hY'
  apply ClovenIsofibration.obj_liftObj I f

lemma eqToHom_comp_liftIso {X Y : D} (f : X ⟶ Y) [IsIso f] {X' X'' : C}
    (hX' : F.obj X' = X) (hX'' : X'' = X') :
    eqToHom hX'' ≫ I.liftIso f hX' =
    I.liftIso f (X' := X'') (by rw [hX'', hX']) ≫ eqToHom (by subst hX''; rfl) := by
  subst hX''
  simp

class IsSplit {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]
    {F : C ⥤ D} (I : ClovenIsofibration F) where
  liftObj_id {X : D} {X' : C} (hX' : F.obj X' = X) : I.liftObj (𝟙 X) hX' = X'
  liftIso_id {X : D} {X' : C} (hX' : F.obj X' = X) : I.liftIso (𝟙 X) hX' =
    eqToHom (liftObj_id hX').symm
  liftObj_comp {X Y Z : D} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [IsIso g] {X' : C}
    (hX' : F.obj X' = X) {Y' : C} (hY' : I.liftObj f hX' = Y') : I.liftObj (f ≫ g) hX' =
    I.liftObj g (X' := Y') (I.liftObj_comp_aux f hX' Y' hY')
  liftIso_comp {X Y Z : D} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [IsIso g] {X' : C}
    (hX' : F.obj X' = X) {Y' : C} (hY' : I.liftObj f hX' = Y') : I.liftIso (f ≫ g) hX' =
    I.liftIso f hX' ≫ eqToHom hY' ≫
    I.liftIso g (X' := Y') (I.liftObj_comp_aux f hX' Y' hY') ≫
    eqToHom (liftObj_comp f g hX' hY').symm

end

open IsSplit

@[simp]
lemma liftObj_eqToHom {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]
    {F : C ⥤ D} (I : ClovenIsofibration F) [IsSplit I] {X Y : D} (h : X = Y) {X' : C}
    (hX' : F.obj X' = X) : I.liftObj (eqToHom h) hX' = X' := by
  subst h
  simp [IsSplit.liftObj_id]

@[simp]
lemma liftIso_eqToHom {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D] (F : C ⥤ D)
    (I : ClovenIsofibration F) [IsSplit I] {X Y : D} (h : X = Y) {X' : C} (hX' : F.obj X' = X) :
    I.liftIso (eqToHom h) hX' = eqToHom (by simp) := by
  subst h
  simp [IsSplit.liftIso_id]

section
variable {Γ : Type u} {E : Type u} [Groupoid.{v} Γ] [Groupoid.{v} E] {F : E ⥤ Γ}
  (I : ClovenIsofibration F)

def classifier.map.obj {X Y : Γ} (f : X ⟶ Y) (a : F.Fiber X) : F.Fiber Y :=
  ⟨I.liftObj f a.2, ClovenIsofibration.obj_liftObj ..⟩

-- Fiber is a semireducible subtype; allow its projections to elaborate in this proof.
set_option backward.isDefEq.respectTransparency false in
def classifier.map.map  {X Y} (f: X ⟶ Y) {a b : F.Fiber X} (m : a ⟶ b) :
    map.obj I f a ⟶ map.obj I f b :=
  let i1 : a.1 ⟶ I.liftObj f a.2 := I.liftIso f a.2
  let i2 := I.liftIso f b.2
  let i := Groupoid.inv i1 ≫ Fiber.fiberInclusion.map m ≫ i2
  have e :𝟙 Y = eqToHom (by simp[obj_liftObj]) ≫
      F.map (CategoryTheory.inv i1 ≫ Fiber.fiberInclusion.map m ≫ i2) ≫
        eqToHom (by simp[obj_liftObj]) := by
       simp [i1, i2, Fiber.functor_map_fiberInclusion_map, Functor.map_inv, map_liftIso']
  have : F.IsHomLift (𝟙 Y) i := by
    simp only[i, e]
    apply IsHomLift.of_fac _ _ _ (ClovenIsofibration.obj_liftObj ..)
      (ClovenIsofibration.obj_liftObj ..)
    simp
  Fiber.homMk F _ i

lemma classifier.map.map_id {X Y} (f : X ⟶ Y) (a: F.Fiber X):
    map.map I f (𝟙 a) = 𝟙 (map.obj I f a) := by
   ext
   simp [map, Fiber.homMk, Fiber.fiberInclusion, classifier.map.obj]
   rfl

-- Allow fiber projections to reduce when simplifying the conjugated composite.
set_option backward.isDefEq.respectTransparency false in
lemma classifier.map.map_comp {X Y} (f: X ⟶ Y) {a b c: F.Fiber X} (m1 : a ⟶ b) (m2: b ⟶ c):
    map.map I f (m1 ≫ m2) = map.map I f m1 ≫ map.map I f m2 := by
   ext
   simp only [Functor.map_comp]
   simp [classifier.map.map, Fiber.homMk, Fiber.fiberInclusion, Category.assoc]

@[simps]
def classifier.map {X Y} (f : X ⟶ Y) : F.Fiber X ⥤ F.Fiber Y where
  obj := classifier.map.obj I f
  map := classifier.map.map I f
  map_id := classifier.map.map_id I f
  map_comp := classifier.map.map_comp I f

variable [IsSplit I]

-- Fiber projections must unfold for the dependent functor extensionality proof.
set_option backward.isDefEq.respectTransparency false in
lemma classifier.map_id (X : Γ) : classifier.map I (𝟙 X) = 𝟙 (Grpd.of (F.Fiber X)) := by
  fapply Functor.ext
  · intro a
    apply Subtype.ext
    simp [map.obj, liftObj_id]
  · intro a b f
    simp
    ext
    simp [map.map, liftIso_id, eqToHom_map]

-- Reduce fiber projections in the dependent composition proof.
set_option backward.isDefEq.respectTransparency false in
lemma classifier.map_comp {X Y Z: Γ} (f : X⟶ Y) (g : Y ⟶ Z):
    classifier.map I (f ≫ g) = classifier.map I f ⋙ classifier.map I g := by
  fapply Functor.ext
  · intro a
    simp[map.obj, liftObj_comp]
  · intro a b f
    simp
    ext
    simp only [map.map, Fiber.fiberInclusion_homMk, Groupoid.inv_eq_inv, ← Category.assoc,
      Functor.map_comp, eqToHom_map, ← heq_eq_eq, heq_comp_eqToHom_iff]
    simp [liftIso_comp,← Category.assoc]

/-- Any split isofibration of groupoids is classified up to isomorphism
as the (groupoidal) Grothendieck construction on the functor `classifier`. -/
def classifier : Γ ⥤ Grpd.{v,u} where
  obj X := Grpd.of (F.Fiber X)
  map f := Grpd.homOf (classifier.map I f)
  map_id _ := classifier.map_id ..
  map_comp _ _ := classifier.map_comp ..

@[simp]
lemma fiberInclusion_obj_classifier_map_obj {x y} (f : x ⟶ y) (p) :
    Fiber.fiberInclusion.obj ((I.classifier.map f).obj p) = I.liftObj f p.2 := by
  rfl

open CategoryTheory.Functor.Groupoidal

def grothendieckClassifierIso.hom.obj (pair: ∫ I.classifier) : E := pair.fiber.1

lemma grothendieckClassifierIso.hom.map_aux {X Y: Γ} (f: X ⟶ Y) (a: I.classifier.obj X) :
    (I.classifier.map f).obj a = ⟨I.liftObj (X' := a.1) f a.2, obj_liftObj ..⟩ := by
  rfl

lemma grothendieckClassifierIso.hom.map_aux2
    (X: Γ) (a: I.classifier.obj X) : F.obj a.1 = X := by
  simp[classifier] at a
  simp[a.2]

def grothendieckClassifierIso.hom.map {p1 p2: ∫ I.classifier} (h: p1 ⟶ p2) :
    (p1.fiber.1 ⟶ p2.fiber.1) :=
  I.liftIso h.base (hom.map_aux2 ..) ≫
  (eqToHom (by simp[grothendieckClassifierIso.hom.map_aux] )) ≫ h.fiber.1

def grothendieckClassifierIso.hom.map' {p1 p2: ∫ I.classifier} (h: p1 ⟶ p2) :
    (p1.fiber.1 ⟶ p2.fiber.1) :=
  I.liftIso h.base (hom.map_aux2 ..) ≫
  (eqToHom (by simp[grothendieckClassifierIso.hom.map_aux,Fiber.fiberInclusion] )) ≫
  Fiber.fiberInclusion.map h.fiber ≫ (eqToHom (by simp[Fiber.fiberInclusion] ))

-- The fiber inclusion and classifier objects are definitionally equal at full transparency.
set_option backward.isDefEq.respectTransparency false in
lemma grothendieckClassifierIso.hom.map_id (X : ∫ I.classifier) :
    hom.map I (𝟙 X) = 𝟙 _ := by
  change I.liftIso (Hom.base (𝟙 X)) (hom.map_aux2 ..) ≫
     eqToHom (by simp [liftObj_id, Fiber.fiberInclusion]) ≫
       Fiber.fiberInclusion.map (Hom.fiber (𝟙 X)) = 𝟙 _
  simp only [Groupoidal.id_base, liftIso_id, Groupoidal.id_fiber]
  rw [eqToHom_map]
  simp

-- Reduce classifier and fiber projections in the dependent composition proof.
set_option backward.isDefEq.respectTransparency false in
lemma grothendieckClassifierIso.hom.map_comp {X Y Z: ∫ I.classifier} (f : X ⟶ Y) (g : Y ⟶ Z) :
    hom.map' I (f ≫ g) = hom.map' I f ≫ hom.map' I g := by
  simp [map', liftIso_comp, eqToHom_map, classifier, classifier.map.map]

-- Reduce fiber projections in the naturality equation.
set_option backward.isDefEq.respectTransparency false in
@[simps!]
def grothendieckClassifierIso.hom.hom {X Y} (f : X ⟶ Y) :
    Fiber.fiberInclusion ⟶ I.classifier.map f ⋙ Fiber.fiberInclusion where
  app _ := I.liftIso f ..
  naturality := by
   intro a b g
   simp[Fiber.fiberInclusion,classifier,classifier.map.map,Fiber.homMk]

-- Reduce dependent classifier and fiber projections in the functor laws.
set_option backward.isDefEq.respectTransparency false in
def grothendieckClassifierIso.hom : ∫ I.classifier ⥤ E :=
  Groupoidal.functorFrom (fun x => Fiber.fiberInclusion)
  (grothendieckClassifierIso.hom.hom I)
  (by intro X; ext;simp[hom.hom,liftIso_id])
  (by intro X Y Z f g; ext; simp[hom.hom,liftIso_comp])

def grothendieckClassifierIso.inv.fibMap {X Y}(f : X ⟶ Y) :
    ((F ⋙ I.classifier).map f).obj ⟨X,rfl⟩  ⟶ ⟨Y, rfl⟩  := by
  refine @Fiber.homMk _ _ _ _ F (F.obj Y) _ _ ?_ ?_
  · exact CategoryTheory.inv (I.liftIso (F.map f) rfl) ≫ f
  · simp
    fapply IsHomLift.of_fac
    · simp[ClovenIsofibration.obj_liftObj]
    · rfl
    · simp[Functor.map_inv,ClovenIsofibration.map_liftIso']

-- Reduce the bundled fiber projections in this dependent identity proof.
set_option backward.isDefEq.respectTransparency false in
lemma grothendieckClassifierIso.inv.fibMap_id (x : E) :
    inv.fibMap I (𝟙 x) = eqToHom (by simp) := by
  apply Fiber.hom_ext
  simp only [comp_obj, comp_map, fibMap, Fiber.fiberInclusion_homMk, Category.comp_id]
  rw![Functor.map_id,liftIso_id]
  simp[inv_eqToHom,eqToHom_map]

-- Reduce the same bundled fiber projections in the composition law.
set_option backward.isDefEq.respectTransparency false in
lemma grothendieckClassifierIso.inv.fibMap_comp {x y z : E} (f : x ⟶ y) (g : y ⟶ z) :
    inv.fibMap I (f ≫ g) =
    eqToHom (by simp) ≫
    (I.classifier.map (F.map g)).map (inv.fibMap I f) ≫ inv.fibMap I g := by
  simp only [comp_obj, comp_map, fibMap]
  apply Fiber.hom_ext
  rw! [Functor.map_comp]
  simp [liftIso_comp, eqToHom_map,classifier,classifier.map.map]

-- Reduce classifier and fiber projections while comparing functor maps.
set_option backward.isDefEq.respectTransparency false in
lemma ι_classifier_comp_forget {x} : ι I.classifier x ⋙ Groupoidal.forget =
    Fiber.fiberInclusion ⋙ F := by
  fapply Functor.ext
  · intro p
    exact p.2.symm
  · intro p q f
    let : F.IsHomLift (𝟙 x) (Fiber.fiberInclusion.map f) := f.2
    simpa using IsHomLift.fac F (𝟙 x) (Fiber.fiberInclusion.map f)

@[simp]
lemma liftObj_map_fiberInclusion_map {S} {X Y : Fiber F S} {X' : E} (f : X ⟶ Y)
    [IsIso (F.map (Fiber.fiberInclusion.map f))] {hX' : X' = Fiber.fiberInclusion.obj X} :
    I.liftObj (F.map (Fiber.fiberInclusion.map f)) (X' := X') (by simp [hX'])
    = Fiber.fiberInclusion.obj X := by
  rw! [Fiber.functor_map_fiberInclusion_map, liftObj_eqToHom, hX']
  rfl

@[simp]
lemma liftIso_map_fiberInclusion_map {S} {X Y : Fiber F S} {X' : E} (f : X ⟶ Y)
    [IsIso (F.map (Fiber.fiberInclusion.map f))] {hX' : X' = Fiber.fiberInclusion.obj X} :
    I.liftIso (F.map (Fiber.fiberInclusion.map f)) (X' := X') (by simp [hX'])
    = eqToHom (by simp [hX']) := by
  rw! [Fiber.functor_map_fiberInclusion_map, liftIso_eqToHom]
  rfl

-- Reduce bundled fiber projections in the classifier isomorphism laws.
set_option backward.isDefEq.respectTransparency false in
open grothendieckClassifierIso in
/-- A split isofibration `F : E ⥤ Γ` is classified by the functor `I.classifier : Γ ⥤ Grpd`.
This means that the (groupoidal) Grothendieck construction on `I.classifier` is isomorphic to
`E` over `Γ`. This isomorphism is called `grothendieckClassifierIso`. -/
def grothendieckClassifierIso : ∫ I.classifier ≅≅ E :=
  Groupoidal.functorIsoFrom (fun x => Fiber.fiberInclusion)
  (hom.hom I) (by intro X; ext; simp [liftIso_id])
  (by intro X Y Z f g; ext; simp [liftIso_comp])
  F (fun x => ⟨x, rfl⟩) (inv.fibMap I) (inv.fibMap_id I) (inv.fibMap_comp I)
  (by simp [ι_classifier_comp_forget])
  (by
    intro x p
    simp only [comp_obj]
    apply Subtype.hext HEq.rfl
    · simp [Functor.Fiber.functor_obj_fiberInclusion_obj]
    · simp [Fiber.fiberInclusion])
  (by
    intro x p q f
    simp only [inv.fibMap]
    apply Fiber.hom_hext
    any_goals apply Fiber.hext
    all_goals simp [Fiber.functor_obj_fiberInclusion_obj q])
  (by intro x; simp [Fiber.fiberInclusion])
  (by
    intro x y f
    simp [inv.fibMap])
  (by simp)
  (by simp [I.map_liftIso'])
  (by
    intro x y f p
    simp only [inv.fibMap]
    apply Fiber.hom_hext
    any_goals apply Fiber.hext
    any_goals simp
    · rw! [map_liftIso', liftObj_comp _ _ _ rfl, liftObj_comp _ _ _ rfl]
      simp [liftObj_eqToHom]
    · simp only [hom.hom]
      rw! (castMode := .all) [map_liftIso', liftIso_comp _ _ _ rfl, liftIso_comp _ _ _ rfl]
      simp only [liftIso_eqToHom, eqToHom_refl, eqToHom_trans, Category.id_comp, Category.assoc,
        IsIso.inv_comp, inv_eqToHom, eqToHom_comp_liftIso, IsIso.inv_hom_id_assoc]
      rw! [eqToHom_heq_id_cod]
      apply eqToHom_heq_id
      rw [liftObj_comp _ _ _ rfl, liftObj_comp _ _ _ rfl]
      simp)

lemma grothendieckClassifierIso.inv_comp_forget :
    (grothendieckClassifierIso I).inv ⋙ Groupoidal.forget = F :=
  rfl

lemma grothendieckClassifierIso.hom_comp_self :
    (grothendieckClassifierIso I).hom ⋙ F = Groupoidal.forget := by
  slice_lhs 2 3 => rw[← inv_comp_forget I (F := F)]
  simp

end

@[simps!]
def iso {A : Type u} [Category.{v} A] {B : Type u₁} [Category.{v₁} B] (F : A ≅≅ B) :
    ClovenIsofibration F.hom where
  liftObj {b0 b1} f hf x hF := F.inv.obj b1
  liftIso {b0 b1} f hf x hF := eqToHom (by simp [← hF, ← Functor.comp_obj]) ≫ F.inv.map f
  isHomLift f hf x hF := IsHomLift.of_fac' _ _ _ hF (by simp [← Functor.comp_obj])
    (by
      simp only [map_comp, eqToHom_map, ← comp_map]
      rw! (castMode := .all) [F.inv_hom_id];
      simp [← heq_eq_eq]
      rfl)
  liftIso_IsIso := by
   intro X Y f i X' hX'
   apply IsIso.comp_isIso

-- The split laws simplify dependent transports through the semireducible `iso` definition.
set_option backward.isDefEq.respectTransparency false in
 instance {A : Type u} [Category.{v} A] {B : Type u₁} [Category.{v₁} B]
     (F : A ≅≅ B) : IsSplit (iso F) where
  liftObj_id h := by simp [← h, ← Functor.comp_obj]
  liftIso_id := by simp
  liftObj_comp := by simp
  liftIso_comp := by simp

section

variable {C : Type u₁} [Groupoid.{v₁,u₁} C] {F : C ⥤ Grpd.{v₂,u₂}}

def forget.liftObj {X Y: C} (f : X ⟶ Y)
    {X' : F.Groupoidal} (hX': Groupoidal.forget.obj X' = X) : F.Groupoidal :=
  Groupoidal.transport (C := C) (c := Y) X' (eqToHom (by subst hX'; simp) ≫ f)

def forget.liftIso {X Y: C} (f : X ⟶ Y) {X' : F.Groupoidal} (hX': Groupoidal.forget.obj X' = X) :
    X' ⟶ forget.liftObj f hX' :=
  Groupoidal.toTransport X' (eqToHom (by subst hX'; simp) ≫ f)

-- Unfold the semireducible transport and forgetful functor in the lift equation.
set_option backward.isDefEq.respectTransparency false in
lemma forget.isHomLift {X Y: C} (f : X ⟶ Y) {X' : F.Groupoidal}
    (hX': Groupoidal.forget.obj X' = X) : Groupoidal.forget.IsHomLift f (forget.liftIso f hX') := by
  subst X
  apply IsHomLift.of_fac' (ha := rfl) (hb := by simp [liftObj])
  simp [liftIso, Groupoidal.forget_map, Groupoidal.toTransport_base]

theorem toTransport_IsIso (x : F.Groupoidal) {c : C} (t : x.base ⟶ c) :
    IsIso (Groupoidal.toTransport x t) :=
  inferInstance

variable (F) in
@[simps!]
def forget : ClovenIsofibration (Groupoidal.forget (F := F)) where
  liftObj f := forget.liftObj f
  liftIso f := forget.liftIso f
  isHomLift f := forget.isHomLift f
  liftIso_IsIso := inferInstance

instance {X Y: C} (f : X ⟶ Y) [IsIso f] {X' : F.Groupoidal}
    (hX': Groupoidal.forget.obj X' = X) : IsIso (forget.liftIso f hX') := by
  apply toTransport_IsIso

theorem forget.liftObj_id {X: C} {X' : F.Groupoidal} (hX': Groupoidal.forget.obj X' = X) :
    forget.liftObj (𝟙 X) hX' = X' := by
  simp [liftObj, Groupoidal.transport_eqToHom]

-- The cast and transport equations require unfolding semireducible definitions.
set_option backward.isDefEq.respectTransparency false in
theorem forget.liftIso_id {X: C} {X' : F.Groupoidal} (hX': Groupoidal.forget.obj X' = X) :
    forget.liftIso (𝟙 X) hX' = eqToHom (by simp [forget.liftObj_id]) := by
  dsimp [liftIso]
  rw! (castMode :=.all)[Category.comp_id]
  simp only [Groupoidal.toTransport_eqToHom, ← heq_eq_eq, eqRec_heq_iff]
  congr!

-- Unfold transport projections when simplifying dependent casts.
set_option backward.isDefEq.respectTransparency false in
lemma forget.liftObj_comp {X Y Z: C} (f : X ⟶ Y) (g : Y ⟶ Z)
    {X' : F.Groupoidal} (hX' : X'.base = X)
    {Y' : F.Groupoidal} (hY' : forget.liftObj f hX' = Y') :
    forget.liftObj (f ≫ g) hX' = forget.liftObj g (liftObj_comp_aux (forget F) f hX' Y' hY') := by
  subst hX' hY'
  simp [liftObj, Groupoidal.transport, Grothendieck.transport, Functor.map_comp,
    Grpd.comp_eq_comp, Grpd.forgetToCat]

-- Unfold transport projections when rewriting dependent casts.
set_option backward.isDefEq.respectTransparency false in
lemma forget.liftIso_comp {X Y Z: C} (f : X ⟶ Y) (g : Y ⟶ Z) {X' : F.Groupoidal}
    (hX' : X'.base = X) {Y' : F.Groupoidal} (hY' : forget.liftObj f hX' = Y') :
    forget.liftIso (f ≫ g) hX' = forget.liftIso f hX' ≫ eqToHom hY' ≫
    forget.liftIso g (liftObj_comp_aux (forget F) f hX' Y' hY') ≫
    eqToHom (by symm; apply forget.liftObj_comp; assumption) := by
  subst hX' hY'
  simp only [liftIso, eqToHom_refl, Groupoidal.toTransport_comp, Groupoidal.toTransport_id,
    Category.assoc, eqToHom_trans, Category.id_comp, eqToHom_trans_assoc]
  congr 2
  simp only [liftObj, eqToHom_refl, ← Category.assoc, ← heq_eq_eq, heq_comp_eqToHom_iff,
    heq_eqToHom_comp_iff, comp_eqToHom_heq_iff]
  congr 1
  rw [Groupoidal.transport_congr ((X'.transport (𝟙 X'.base))) X' (by rw[Groupoidal.transport_id])
    f f (by simp), Groupoidal.transport_congr (X'.transport (𝟙 X'.base ≫ f)) (X'.transport f) _
    ((𝟙 (X'.transport (𝟙 X'.base ≫ f)).base)) (eqToHom (by simp))]
  all_goals simp [Groupoidal.transport_id]

instance : IsSplit (forget F) where
  liftObj_id := forget.liftObj_id
  liftIso_id := forget.liftIso_id
  liftObj_comp _ _ _ _ := by apply forget.liftObj_comp
  liftIso_comp _ _ _ _ := by apply forget.liftIso_comp

end

def id (A : Type u) [Category.{v} A] : ClovenIsofibration (𝟭 A) :=
  iso (Functor.Iso.refl _)

instance (A : Type u) [Category.{v} A] : IsSplit (id A) :=
  inferInstanceAs <| IsSplit (iso (Functor.Iso.refl _))

section

variable {A B C : Type*} [Category A] [Category B] [Category C] {F : A ⥤ B}
  (IF : ClovenIsofibration F) {G : B ⥤ C} (IG : ClovenIsofibration G)

def comp.liftObj {X Y: C} (f: X ⟶ Y) [IsIso f] {X': A} (hX': (F ⋙ G).obj X' = X) : A :=
  let f1 := IG.liftIso (X' := F.obj X') f (by simp at hX'; assumption)
  IF.liftObj (X' := X') f1 rfl

lemma comp.obj_liftObj {X Y: C} (f: X ⟶ Y) [IsIso f] {X': A} (hX': (F ⋙ G).obj X' = X) :
    (F ⋙ G).obj (liftObj IF IG f hX') = Y := by
  simp [liftObj]

def comp.liftIso {X Y: C} (f: X ⟶ Y) [IsIso f] {X': A} (hX': (F ⋙ G).obj X' = X) :
    X' ⟶ comp.liftObj IF IG f hX' :=
  let f1 := IG.liftIso (X' := F.obj X') f (by simp at hX'; assumption)
  IF.liftIso (X' := X') f1 rfl

-- The composite lift contains dependent projections that must unfold during unification.
set_option backward.isDefEq.respectTransparency false in
lemma comp.isHomLift {X Y: C} (f: X ⟶ Y) [IsIso f] {X': A} (hX': (F ⋙ G).obj X' = X) :
    (F ⋙ G).IsHomLift f (comp.liftIso IF IG f hX') := by
  refine IsHomLift.of_fac (F ⋙ G) f (comp.liftIso IF IG f hX') hX'
    (comp.obj_liftObj IF IG f hX') ?_
  simp [comp.liftIso, comp.liftObj, map_liftIso', eqToHom_map, Category.assoc]

/-- `IsMultiplicative` 1/2 -/
@[simps!]
def comp : ClovenIsofibration (F ⋙ G) where
  liftObj := comp.liftObj IF IG
  liftIso := comp.liftIso IF IG
  isHomLift := comp.isHomLift IF IG
  liftIso_IsIso := by
   intro X Y f i1 X' hX'
   simp [comp.liftIso]
   apply liftIso_IsIso

lemma comp.liftIso_comp_aux {X Y Z : C} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [IsIso g] {X' : A}
    (hX' : (F ⋙ G).obj X' = X) (Y' : A) (hY' : comp.liftObj IF IG f hX' = Y') :
    G.obj (F.obj Y') = Y := by
  subst hY'; simp [comp.liftObj]

variable [IsSplit IF] [IsSplit IG]

lemma comp.liftObj_id {X: C} {X': A} (hX': (F ⋙ G).obj X' = X):
    comp.liftObj IF IG (𝟙 X) hX' = X' := by
  simp [comp.liftObj,liftIso_id]

lemma comp.liftIso_id {X : C} {X' : A} (hX' : (F ⋙ G).obj X' = X) :
    comp.liftIso IF IG (𝟙 X) hX' = eqToHom (by simp[comp.liftObj_id]) := by
  dsimp [comp.liftIso]
  rw! (castMode := .all) [IsSplit.liftIso_id]
  simp only [liftIso_eqToHom]
  apply eq_of_heq
  apply (eqRec_heq_iff).2
  apply HEq.trans (eqToHom_heq_id_dom _ _ _) (eqToHom_heq_id_dom _ _ _).symm

-- The congruence proof compares dependent lifts after unfolding the composite.
set_option backward.isDefEq.respectTransparency false in
lemma comp.liftObj_comp {X Y Z : C} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [IsIso g] {X' : A}
    (hX' : (F ⋙ G).obj X' = X) :
    comp.liftObj IF IG (f ≫ g) hX' =
    comp.liftObj (X' := comp.liftObj IF IG f hX') IF IG g
    (by simp only[comp.obj_liftObj]) := by
  simp only [liftObj, liftIso_comp, eqToHom_refl, Category.id_comp, IsSplit.liftObj_comp,
    liftObj_eqToHom]
  congr!
  simp

-- The dependent rewrite compares casts whose definitions need semireducible unfolding.
set_option backward.isDefEq.respectTransparency false in
lemma comp.liftIso_comp {X Y Z : C} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [IsIso g] {X' : A}
    (hX' : (F ⋙ G).obj X' = X) (Y' : A)
    (hY' : comp.liftObj IF IG f hX' = Y') :
    comp.liftIso IF IG (f ≫ g) hX' = comp.liftIso IF IG f hX' ≫ eqToHom hY' ≫
    comp.liftIso IF IG g (by subst hY';simp[liftObj]) ≫
    eqToHom (by subst hY'; simp[comp.liftObj_comp]) := by
  subst hY'
  simp only [liftObj, liftIso]
  rw! [IsSplit.liftIso_comp (I := IG) f g hX' rfl, eqToHom_refl, Category.id_comp]
  simp only [IsSplit.liftIso_comp, eqToHom_refl, liftIso_eqToHom, eqToHom_trans, Category.id_comp,
    Category.assoc]
  congr 1
  simp only [← heq_eq_eq, heq_comp_eqToHom_iff, comp_eqToHom_heq_iff]
  congr!
  simp

instance : IsSplit (comp IF IG) where
  liftObj_id  := by
    intro X X' hX'
    apply comp.liftObj_id
  liftIso_id := by
    intro X X' hX'
    apply comp.liftIso_id
  liftObj_comp := by
    intro X Y Z f i1 g i2 X' hX' Y' hY'
    subst hY'
    apply comp.liftObj_comp
  liftIso_comp := by
    intro X Y Z f i1 g i2 X' hX' Y' hY'
    apply comp.liftIso_comp

section isoComp

@[simps]
def ofEq (F' : A ⥤ B) (hF' : F = F') : ClovenIsofibration F' where
  liftObj f hf a ha := IF.liftObj f (by convert ha)
  liftIso f hf a ha := IF.liftIso f (by convert ha)
  isHomLift f hf a ha := by
    subst hF'
    apply IF.isHomLift
  liftIso_IsIso := by
    subst hF'
    exact IF.liftIso_IsIso

instance (F' : A ⥤ B) (hF' : F = F') : (ofEq IF F' hF').IsSplit := by
  subst hF'
  exact inferInstanceAs IF.IsSplit

variable {A' : Type u₁} [Category.{v₁} A']
    (i : A' ≅≅ A) (F' : A' ⥤ B) (hF' : F' = i.hom ⋙ F)

def isoComp : ClovenIsofibration F' :=
  ofEq (comp (iso ..) IF) F' hF'.symm

instance : IsSplit (isoComp IF i F' hF') :=
  inferInstanceAs (ofEq ..).IsSplit

end isoComp

end

def ofIsPullback {A B A' B' : Type u} [Groupoid.{v} A] [Groupoid.{v} B] [Groupoid.{v} A']
    [Groupoid.{v} B'] (top : A' ⥤ A) (F' : A' ⥤ B') (F : A ⥤ B) (bot : B' ⥤ B)
    (isPullback : Functor.IsPullback top F' F bot) (IF : ClovenIsofibration F) [IsSplit IF] :
    ClovenIsofibration F' :=
  let i : Functor.Groupoidal IF.classifier ≅≅ A :=
    Functor.ClovenIsofibration.grothendieckClassifierIso ..
  have i_comp_F : i.hom ⋙ F = Groupoidal.forget := by
    simp [i, grothendieckClassifierIso.hom_comp_self]
  have eq1 : Groupoidal.pre IF.classifier bot ⋙ Groupoidal.forget = Groupoidal.forget ⋙ bot := by
    simp [Groupoidal.pre_comp_forget]
  have q1 : Functor.IsPullback (Groupoidal.pre IF.classifier bot ⋙ i.hom)
      (Groupoidal.forget (F := (bot ⋙ IF.classifier))) F bot :=
    Functor.IsPullback.Paste.horiz eq1 (by simp [i_comp_F])
    (Groupoidal.pre_isPullback ..)
    (Functor.IsPullback.ofBotId i_comp_F.symm)
  let j : A' ≅≅ Functor.Groupoidal (F := bot ⋙ IF.classifier) :=
    Functor.IsPullback.isoIsPullback isPullback q1
  have e : F' = j.hom ⋙ (Groupoidal.forget (F := bot ⋙ IF.classifier)) :=
    (IsPullback.isoIsPullback.hom_comp_right' isPullback q1 (hom := j.hom) (by simp[j])).symm
  isoComp (Functor.ClovenIsofibration.forget ..) j _ e

instance {A B A' B' : Type u} [Groupoid.{v} A] [Groupoid.{v} B] [Groupoid.{v} A']
    [Groupoid.{v} B'] (top : A' ⥤ A) (F' : A' ⥤ B') (F : A ⥤ B) (bot : B' ⥤ B)
    (isPullback : Functor.IsPullback top F' F bot) (IF : ClovenIsofibration F) [IsSplit IF] :
    IsSplit (ofIsPullback top F' F bot isPullback IF) := by
  dsimp [ofIsPullback]
  infer_instance

end ClovenIsofibration
end
end Functor
end CategoryTheory

namespace GroupoidModel

open CategoryTheory Functor.ClovenIsofibration

def tpClovenIsofibration : (GroupoidModel.U.{u}.tp).ClovenIsofibration :=
  let i : U.{u}.Tm ≅≅ Functor.Groupoidal (F := Core.inclusion _ ⋙ AsSmall.down) :=
    Functor.IsPullback.isoIsPullback IsPullback.isPullbackCoreAsSmall'
      (Functor.Groupoidal.isPullback (Core.inclusion _ ⋙ AsSmall.down))
  isoComp (Functor.ClovenIsofibration.forget _) i
  _ (Functor.IsPullback.isoIsPullback.hom_comp_right ..).symm

-- Instance search must unfold the functor data to match the split iso-composite.
set_option backward.isDefEq.respectTransparency false in
instance : IsSplit tpClovenIsofibration := by
  dsimp only [tpClovenIsofibration]
  infer_instance

end GroupoidModel
