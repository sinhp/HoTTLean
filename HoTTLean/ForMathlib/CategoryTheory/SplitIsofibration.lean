import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.FiberedCategory.HomLift
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import HoTTLean.Grothendieck.Groupoidal.IsPullback
import HoTTLean.Grothendieck.Groupoidal.Basic
universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section

namespace CategoryTheory

lemma eqToHom_heq_id {C : Type*} [Category C] (x y z : C) (h : x = y)
    (hz : z = x) : eqToHom h ≍ 𝟙 z := by cat_disch

namespace Functor

namespace Fiber
section

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]
variable {p : 𝒳 ⥤ 𝒮} {S : 𝒮}

@[simp]
lemma functor_obj_fiberInclusion_obj (a : Fiber p S) :
    p.obj (Fiber.fiberInclusion.obj a) = S := by
  exact a.2

lemma functor_map_fiberInclusion_map {a b : Fiber p S}
    (f : a ⟶ b) :
    p.map (Fiber.fiberInclusion.map f) = eqToHom (by simp) := by
  have H := f.2
  simpa using IsHomLift.fac' p (𝟙 S) f.1

lemma hext {S'} (hS : S' ≍ S) {a : Fiber p S}
    {a' : Fiber p S'} (h : Fiber.fiberInclusion.obj a ≍ Fiber.fiberInclusion.obj a') : a ≍ a' := by
  subst hS
  simpa using Subtype.ext h.eq

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
    ⟨Fiber.homMk F _ (CategoryTheory.inv f.1), by cat_disch, by cat_disch⟩ }

instance {X : Γ} : Groupoid (F.Fiber X) := Groupoid.ofIsGroupoid

end Fiber
section
variable {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]

structure ClovenIsofibration (F : C ⥤ D) where
  liftObj {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) : C
  liftIso {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) : X' ⟶ liftObj f hX'
  isHomLift {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) :
    F.IsHomLift f (liftIso f hX')
  liftIso_IsIso {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) :
   IsIso (liftIso f hX')



section
variable {F : C ⥤ D} (I : ClovenIsofibration F)

instance {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) :
  F.IsHomLift f (I.liftIso f hX') := I.isHomLift f hX'

instance liftIso_IsIso {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X):
  IsIso (ClovenIsofibration.liftIso I f hX') := ClovenIsofibration.liftIso_IsIso I f hX'


@[simp]
lemma ClovenIsofibration.obj_liftObj {X Y : D} (f : X ⟶ Y) [IsIso f]
    {X' : C} (hX' : F.obj X' = X) : F.obj (I.liftObj f hX') = Y :=
  IsHomLift.codomain_eq F f (I.liftIso f hX')

lemma ClovenIsofibration.map_liftIso {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C}
    (hX' : F.obj X' = X) :
  eqToHom hX'.symm ≫ F.map (I.liftIso f hX') ≫ eqToHom (obj_liftObj ..) = f := by
  have i : F.IsHomLift f (I.liftIso f hX') := I.isHomLift ..
  symm
  apply IsHomLift.fac

lemma ClovenIsofibration.map_liftIso' {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C}
    (hX' : F.obj X' = X) : F.map (I.liftIso f hX') =
    eqToHom hX' ≫ f ≫ eqToHom (by simp[obj_liftObj]) := by
    simp[← map_liftIso I f hX']

lemma ClovenIsofibration.liftObj_comp_aux {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C}
    (hX' : F.obj X' = X) (Y' : C) (hY' : I.liftObj f hX' = Y') : F.obj Y' = Y := by
  subst hY'
  apply ClovenIsofibration.obj_liftObj I f

lemma ClovenIsofibration.eqToHom_comp_liftIso {X Y : D} (f : X ⟶ Y) [IsIso f] {X' X'' : C}
    (hX' : F.obj X' = X) (hX'' : X'' = X') :
    eqToHom hX'' ≫ I.liftIso f hX' =
    I.liftIso f (X' := X'') (by rw [hX'', hX']) ≫ eqToHom (by subst hX''; rfl) := by
  subst hX''
  simp

end

structure SplitIsofibration {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]
    (F : C ⥤ D) extends ClovenIsofibration F where
  liftObj_id {X : D} {X' : C} (hX' : F.obj X' = X) : liftObj (𝟙 X) hX' = X'
  liftIso_id {X : D} {X' : C} (hX' : F.obj X' = X) : liftIso (𝟙 X) hX' =
    eqToHom (liftObj_id hX').symm
  liftObj_comp {X Y Z : D} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [IsIso g] {X' : C}
    (hX' : F.obj X' = X) (Y' : C) (hY' : liftObj f hX' = Y') : liftObj (f ≫ g) hX' =
    liftObj g (X' := Y') (toClovenIsofibration.liftObj_comp_aux f hX' Y' hY')
  liftIso_comp {X Y Z : D} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [IsIso g] {X' : C}
    (hX' : F.obj X' = X) (Y' : C) (hY' : liftObj f hX' = Y') : liftIso (f ≫ g) hX' =
    liftIso f hX' ≫ eqToHom hY' ≫
    liftIso g (X' := Y') (toClovenIsofibration.liftObj_comp_aux f hX' Y' hY') ≫
    eqToHom (liftObj_comp f g hX' Y' hY').symm


end
namespace SplitIsofibration

open ClovenIsofibration

@[simp]
lemma liftObj_eqToHom {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]
    (F : C ⥤ D) (I : SplitIsofibration F) {X Y : D} (h : X = Y) {X' : C}
    (hX' : F.obj X' = X) : I.liftObj (eqToHom h) hX' = X' := by
  subst h
  simp [SplitIsofibration.liftObj_id]

@[simp]
lemma liftIso_eqToHom {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D] (F : C ⥤ D)
    (I : SplitIsofibration F) {X Y : D} (h : X = Y) {X' : C} (hX' : F.obj X' = X) :
    I.liftIso (eqToHom h) hX' = eqToHom (by simp) := by
  subst h
  simp [SplitIsofibration.liftIso_id]

section
variable {Γ : Type u} {E : Type u} [Groupoid.{v} Γ] [Groupoid.{v} E] {F : E ⥤ Γ}
  (I : SplitIsofibration F)




/-- Any isofibration `F : E ⥤ Γ` of groupoids is classified by a functor `classifier : Γ ⥤ Grpd`.
-/
def classifier.map.obj {X Y : Γ} (f : X ⟶ Y) (a : F.Fiber X) : F.Fiber Y :=
  ⟨I.liftObj f a.2, ClovenIsofibration.obj_liftObj ..⟩

def classifier.map.map  {X Y} (f: X ⟶ Y) {a b : F.Fiber X} (m : a ⟶ b) :
    map.obj I f a ⟶ map.obj I f b :=
  let i1 : a.1 ⟶ I.liftObj f a.2 := I.liftIso f a.2
  let i2 := I.liftIso f b.2
  let i := Groupoid.inv i1 ≫ Fiber.fiberInclusion.map m ≫ i2
  have e :𝟙 Y = eqToHom (by simp[obj_liftObj]) ≫
     F.map (CategoryTheory.inv i1 ≫ Fiber.fiberInclusion.map m ≫ i2) ≫ eqToHom (by simp[obj_liftObj])
     := by simp[i1, i2, Fiber.functor_map_fiberInclusion_map, Functor.map_inv,map_liftIso']
  have : F.IsHomLift (𝟙 Y) i := by
    simp only[i, e]
    apply IsHomLift.of_fac _ _ _ (ClovenIsofibration.obj_liftObj ..)
      (ClovenIsofibration.obj_liftObj ..)
    simp
  Fiber.homMk F _ i


lemma classifier.map.map_id {X Y} (f : X ⟶ Y) (a: F.Fiber X):
  map.map I f (𝟙 a) = 𝟙 (map.obj I f a) := by
   ext
   simp[classifier.map.map]
   simp[Fiber.fiberInclusion]
   --simp[CategoryStruct.id]
   simp[classifier.map.obj]

lemma classifier.map.map_comp {X Y} (f: X ⟶ Y) {a b c: F.Fiber X} (m1 : a ⟶ b) (m2: b ⟶ c):
  map.map I f (m1 ≫ m2) = map.map I f m1 ≫ map.map I f m2 := by
   ext
   simp[classifier.map.map]
   --simp[CategoryStruct.comp]

@[simps]
def classifier.map {X Y} (f : X ⟶ Y) : F.Fiber X ⥤ F.Fiber Y where
  obj := classifier.map.obj I f
  map := classifier.map.map I f
  map_id := classifier.map.map_id I f
  map_comp := classifier.map.map_comp I f

lemma classifier.map_id (X : Γ) : classifier.map I (𝟙 X) = 𝟙 (Grpd.of (F.Fiber X)) := by
  fapply Functor.ext
  · intro a
    apply Subtype.ext
    simp [map.obj, I.liftObj_id]
  · intro a b f
    simp
    ext
    simp [map.map, I.liftIso_id, eqToHom_map, Grpd.id_eq_id, ← heq_eq_eq]
    --rfl


lemma classifier.map_comp {X Y Z: Γ} (f : X⟶ Y) (g : Y ⟶ Z):
 classifier.map I (f ≫ g) = classifier.map I f ⋙ classifier.map I g := by
  fapply Functor.ext
  · intro a
    simp[map.obj, I.liftObj_comp]
  · intro a b f
    simp
    ext
    simp [map.map,  eqToHom_map, Grpd.id_eq_id, ← heq_eq_eq,← Category.assoc]
    simp[I.liftIso_comp,← Category.assoc]
    --congr 1
    --simp[Category.assoc]
    --congr
   -- simp[]



def classifier : Γ ⥤ Grpd.{v,u} where
  obj X := Grpd.of (F.Fiber X)
  map f := Grpd.homOf (classifier.map I f)
  map_id _ := classifier.map_id ..
  map_comp _ _ := classifier.map_comp ..

@[simp]
lemma fiberInclusion_obj_classifier_map_obj {x y} (f : x ⟶ y) (p) :
    Fiber.fiberInclusion.obj ((I.classifier.map f).obj p) = I.liftObj f p.2 := by
  simp [classifier, classifier.map.obj, Fiber.fiberInclusion]

open CategoryTheory.Functor.Groupoidal

/-- The Grothendieck construction on the classifier is isomorphic to `E`.
TODO: add commuting triangles for `Grothendieck.forget` and `F` with `.hom` and `.inv`.
TODO: draw pullback diagram. -/

def grothendieckClassifierIso.hom.obj (pair: ∫ I.classifier) : E := pair.fiber.1


lemma grothendieckClassifierIso.hom.map_aux
 {X Y: Γ} (f: X ⟶ Y) (a: I.classifier.obj X)
 : (I.classifier.map f).obj a = ⟨I.liftObj (X' := a.1) f a.2, obj_liftObj ..⟩ := by
  simp[classifier,classifier.map.obj]



/-

Want: F.obj ↑p1.fiber = p1.base

p1 : ∫ I.classifier

p1.base : Γ

p1.fiber : I.classifier.obj p1.base

 Grpd.of (F.Fiber p1.base) =
I.classifier.obj p1.base = F.Fiber p1.base

p1.fiber : F.Fiber p1.base

F.obj p1.fiber = p1.base

-/
#check Functor.ext
lemma grothendieckClassifierIso.hom.map_aux2
 (X: Γ) (a: I.classifier.obj X) : F.obj a.1 = X := by
  simp[classifier] at a
  simp[a.2]


def grothendieckClassifierIso.hom.map {p1 p2: ∫ I.classifier} (h: p1 ⟶ p2) :
 (p1.fiber.1 ⟶ p2.fiber.1) :=
  I.liftIso h.base
   (hom.map_aux2 ..) ≫ (eqToHom (by simp[grothendieckClassifierIso.hom.map_aux] )) ≫
   h.fiber.1


def grothendieckClassifierIso.hom.map' {p1 p2: ∫ I.classifier} (h: p1 ⟶ p2) :
 (p1.fiber.1 ⟶ p2.fiber.1) :=
  I.liftIso h.base
   (hom.map_aux2 ..) ≫
   (eqToHom (by simp[grothendieckClassifierIso.hom.map_aux,Fiber.fiberInclusion] )) ≫
   Fiber.fiberInclusion.map h.fiber ≫
   (eqToHom (by simp[Fiber.fiberInclusion] ))



lemma grothendieckClassifierIso.hom.map_id (X : ∫ I.classifier) :
    hom.map I (𝟙 X) = 𝟙 _ := by
  convert_to _ ≫ _ ≫ Fiber.fiberInclusion.map (Hom.fiber (𝟙 X)) = _
  simp [liftIso_id, eqToHom_map]


lemma grothendieckClassifierIso.hom.map_comp {X Y Z: ∫ I.classifier} (f : X ⟶ Y) (g : Y ⟶ Z) :
    hom.map' I (f ≫ g) = hom.map' I f ≫ hom.map' I g := by
  simp [map', liftIso_comp, eqToHom_map, classifier, classifier.map.map]

@[simps!]
def grothendieckClassifierIso.hom.hom {X Y} (f : X ⟶ Y) :
    Fiber.fiberInclusion ⟶ I.classifier.map f ⋙ Fiber.fiberInclusion where
  app _ := I.liftIso f ..
  naturality := by
   intro a b g
   simp[Fiber.fiberInclusion,classifier,classifier.map.map,Fiber.homMk]


def grothendieckClassifierIso.hom : ∫ I.classifier ⥤ E :=
  Groupoidal.functorFrom (fun x => Fiber.fiberInclusion)
  (grothendieckClassifierIso.hom.hom I)
    (by intro X; ext;simp[hom.hom,liftIso_id])
    (by intro X Y Z f g; ext; simp[hom.hom,liftIso_comp])

def grothendieckClassifierIso.inv.fibMap {X Y}(f : X ⟶ Y) :
 ((F ⋙ I.classifier).map f).obj ⟨X,rfl⟩  ⟶ ⟨Y, rfl⟩  := by
  -- simp[classifier,classifier.map.obj]
  refine @Fiber.homMk _ _ _ _ F (F.obj Y) _ _ ?_ ?_
  · exact CategoryTheory.inv (I.liftIso (F.map f) rfl) ≫ f
  · simp
    fapply IsHomLift.of_fac
    · simp[ClovenIsofibration.obj_liftObj]
    · rfl
    · simp[Functor.map_inv,ClovenIsofibration.map_liftIso']

lemma grothendieckClassifierIso.inv.fibMap_id (x : E) :
    inv.fibMap I (𝟙 x) = eqToHom (by simp) := by
  apply Fiber.hom_ext
  simp [inv.fibMap]
  rw![Functor.map_id,liftIso_id]
  simp[inv_eqToHom,eqToHom_map]

lemma grothendieckClassifierIso.inv.fibMap_comp {x y z : E} (f : x ⟶ y) (g : y ⟶ z) :
    inv.fibMap I (f ≫ g) =
    eqToHom (by simp) ≫
    (I.classifier.map (F.map g)).map (inv.fibMap I f) ≫ inv.fibMap I g := by
  simp[inv.fibMap]
  apply Fiber.hom_ext
  rw![Functor.map_comp]
  simp[liftIso_comp]
  simp[eqToHom_map,classifier,classifier.map.map]


lemma ι_classifier_comp_forget {x} : ι I.classifier x ⋙ Groupoidal.forget =
    Fiber.fiberInclusion ⋙ F := by
  fapply Functor.ext
  · intro p
    exact p.2.symm
  · intro p q f
    simpa using IsHomLift.fac ..

lemma _root_.Subtype.hext {α α' : Sort u} (hα : α ≍ α') {p : α → Prop} {p' : α' → Prop}
    (hp : p ≍ p') {a : { x // p x }} {a' : { x // p' x }} (ha : a.1 ≍ a'.1) : a ≍ a' := by
  subst hα hp
  simp only [heq_eq_eq]
  ext
  simpa [← heq_eq_eq]

@[simp]
lemma liftObj_map_fiberInclusion_map {S} {X Y : Fiber F S} {X' : E} (f : X ⟶ Y)
    [IsIso (F.map (Fiber.fiberInclusion.map f))] {hX' : X' = Fiber.fiberInclusion.obj X} :
    I.liftObj (F.map (Fiber.fiberInclusion.map f)) (X' := X') (by simp [hX'])
    = Fiber.fiberInclusion.obj X := by
  rw! [Fiber.functor_map_fiberInclusion_map, liftObj_eqToHom, hX']

@[simp]
lemma liftIso_map_fiberInclusion_map {S} {X Y : Fiber F S} {X' : E} (f : X ⟶ Y)
    [IsIso (F.map (Fiber.fiberInclusion.map f))] {hX' : X' = Fiber.fiberInclusion.obj X} :
    I.liftIso (F.map (Fiber.fiberInclusion.map f)) (X' := X') (by simp [hX'])
    = eqToHom (by simp [hX']) := by
  rw! [Fiber.functor_map_fiberInclusion_map, liftIso_eqToHom]

open grothendieckClassifierIso in
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
    · rw! [map_liftIso', I.liftObj_comp _ _ _ _ rfl, I.liftObj_comp _ _ _ _ rfl]
      simp [liftObj_eqToHom]
    · rw! [map_liftIso', I.liftIso_comp _ _ _ _ rfl, I.liftIso_comp _ _ _ _ rfl]
      simp only [liftIso_eqToHom, eqToHom_refl, eqToHom_trans, Category.id_comp, Category.assoc,
        IsIso.inv_comp, inv_eqToHom, eqToHom_comp_liftIso, IsIso.inv_hom_id_assoc]
      rw! [eqToHom_heq_id_cod]
      apply eqToHom_heq_id
      rw [I.liftObj_comp _ _ _ _ rfl, I.liftObj_comp _ _ _ _ rfl]
      simp)


end

def iso {A B : Type u} [Category.{v} A] [Category.{v} B] (F : A ≅≅ B) :
    SplitIsofibration F.hom where
  liftObj {b0 b1} f hf x hF := F.inv.obj b1
  liftIso {b0 b1} f hf x hF := eqToHom (by simp [← hF, ← Functor.comp_obj]) ≫ F.inv.map f
  isHomLift f hf x hF := IsHomLift.of_fac' _ _ _ hF (by simp [← Functor.comp_obj])
    (by
      simp only [map_comp, eqToHom_map, ← comp_map]
      rw! (castMode := .all) [F.inv_hom_id];
      simp [← heq_eq_eq]
      rfl)
  liftObj_id h := by simp [← h, ← Functor.comp_obj]
  liftIso_id := by simp
  liftObj_comp := by simp
  liftIso_comp := by simp
  liftIso_IsIso := by
   intro X Y f i X' hX'
   apply IsIso.comp_isIso


section

variable {C : Type u₁} [Groupoid.{v₁,u₁} C] {F : C ⥤ Grpd.{v₂,u₂}}

def forget.liftObj {X Y: C} (f : X ⟶ Y)
     {X' : F.Groupoidal} (hX': Groupoidal.forget.obj X' = X) : F.Groupoidal
  := Groupoidal.transport (C := C) (c := Y) X' (eqToHom (by subst hX'; simp) ≫ f)

def forget.liftIso {X Y: C} (f : X ⟶ Y)
    {X' : F.Groupoidal} (hX': Groupoidal.forget.obj X' = X) :
    X' ⟶ forget.liftObj f hX'
  := Groupoidal.toTransport X' (eqToHom (by subst hX'; simp) ≫ f)


def forget.isHomLift {X Y: C} (f : X ⟶ Y)
     {X' : F.Groupoidal} (hX': Groupoidal.forget.obj X' = X) :
  Groupoidal.forget.IsHomLift f (forget.liftIso f hX') := by
  apply IsHomLift.of_fac' (ha := hX') (hb := by simp[liftObj])
  simp[liftIso]

def toTransport_IsIso (x : F.Groupoidal) {c : C} (t : x.base ⟶ c)  :
    IsIso (Groupoidal.toTransport x t) := by infer_instance
    --  let tinv := (asIso t).inv
    --  let tinv': (x.transport t).base ⟶ x.base := (asIso t).inv
    --  let f1 := Groupoidal.toTransport (x.transport t) tinv'
    --  exact ⟨f1 ≫ eqToHom
    --   (by simp[tinv'];
    --       fapply Groupoidal.ext
    --       · simp
    --       · simp
    --         simp[← Functor.comp_obj,← Grpd.comp_eq_comp]

    --         --sorry --previous proof below
    --         -- simp only [eqToHom_refl, map_id, Grpd.id_eq_id, Groupoidal.transport_fiber,
    --         -- id_obj]
    --         -- simp only[← Functor.comp_obj]
    --         -- --simp[← Grothendieck.map_comp_eq]
    --         -- simp only [← Functor.map_comp,← Grpd.comp_eq_comp]
    --         -- simp
    --         ) ,
    --  sorry⟩

def forget.liftIso_IsIso {X Y: C} (f : X ⟶ Y)
    [IsIso f] {X' : F.Groupoidal} (hX': Groupoidal.forget.obj X' = X) :
    IsIso (forget.liftIso f hX')
  := by
   simp[liftIso]
   apply toTransport_IsIso


/-
lemma transport_id {X' : F.Groupoidal}:
  X'.transport (𝟙 X'.base) = X' := by
  fapply Groupoidal.ext
  · simp[Groupoidal.transport,Grothendieck.transport,Groupoidal.base]
  simp[Groupoidal.fiber,Grpd.forgetToCat,Functor.map_id]
  simp[Groupoidal.transport,Grothendieck.transport,Grpd.forgetToCat]
  have e: (F.map (𝟙 X'.base)) = Functor.id _ := by simp
  simp[e]


lemma transport_eqToHom {X: C} {X' : F.Groupoidal} (hX': Groupoidal.forget.obj X' = X):
 X'.transport (eqToHom hX') = X' := by
  subst hX'
  simp[transport_id]
  -- fapply Groupoidal.ext
  -- ·  simp[transport_id]
  --   -- simp[Groupoidal.base]
  -- simp[Groupoidal.fiber,Grpd.forgetToCat,Functor.map_id]
  -- have e: (F.map (𝟙 X'.base)) = Functor.id _ := by simp
  --simp[e]

  should be in groupoidal file
-/

def forget.liftObj_id {X: C} {X' : F.Groupoidal} (hX': Groupoidal.forget.obj X' = X) :
    forget.liftObj (𝟙 X) hX' = X' := by
  simp[liftObj]
  simp[Groupoidal.transport_eqToHom]
  --simp[Groupoidal.transport,Grothendieck.transport]

/-
lemma toTransport_eqToHom {X: C} {X' : F.Groupoidal} (hX': Groupoidal.forget.obj X' = X):
    Groupoidal.toTransport X' (eqToHom hX') = eqToHom (by subst hX'; sorry) := by
  apply Groupoidal.toTransport_eqToHom
-/

  -- subst hX'
  -- simp[Groupoidal.toTransport,Grothendieck.toTransport]
  -- fapply Groupoidal.Hom.ext
  -- · simp[Groupoidal.Hom.base,Groupoidal.base]
  --   rw![Grothendieck.Hom.base]
  --   sorry
  -- sorry

def forget.liftIso_id {X: C} {X' : F.Groupoidal} (hX': Groupoidal.forget.obj X' = X) :
    forget.liftIso (𝟙 X) hX' = eqToHom (by simp[forget.liftObj_id]) := by
  simp[liftIso]
  rw! (castMode :=.all)[Category.comp_id]
  simp[Groupoidal.toTransport_eqToHom]
  simp[← heq_eq_eq]
  congr!


  --conv => rhs ; rw[← toTransport_eqToHom]

  --rw[← toTransport_eqToHom]


  /-simp only [eqToHom_refl, map_id, Grpd.id_eq_id, Groupoidal.transport_fiber,
    --         -- id_obj]
    --         -- simp only[← Functor.comp_obj]
    --         -- --simp[← Grothendieck.map_comp_eq]
    --         -- simp only [← Functor.map_comp,← Grpd.comp_eq_comp]
    --         -- simp
    --         ) ,-/

lemma forget.liftObj_comp {X Y Z: C} (f : X ⟶ Y) (g : Y ⟶ Z)
      {X' : F.Groupoidal} (hX' : X'.base = X)
      (Y' : F.Groupoidal) (hY' : forget.liftObj f hX' = Y')
      (h':  Y'.base = Y := by simp[]):
      forget.liftObj (f ≫ g) hX' = forget.liftObj g h' := by
  simp only [liftObj,Groupoidal.transport_comp]
  simp only [Groupoidal.transport, Grothendieck.transport, comp_obj, comp_map]
  fapply Grothendieck.ext
  · simp
  simp only [Grpd.forgetToCat, Cat.of_α, id_eq, comp_obj, eqToHom_refl, comp_map, map_id,
    Grpd.id_eq_id, id_obj]
  congr!
  simp only [← comp_obj,← Grpd.comp_eq_comp,← Functor.map_comp]
  rw! [eqToHom_map]
  subst hY'
  simp[liftObj,Groupoidal.transport]

lemma forget.liftIso_comp {X Y Z: C} (f : X ⟶ Y) (g : Y ⟶ Z)
      {X' : F.Groupoidal} (hX' : X'.base = X)
      (Y' : F.Groupoidal) (hY' : forget.liftObj f hX' = Y')
      (h':  Y'.base = Y := by simp[])
      (e : liftObj g h' = liftObj (f ≫ g) hX' := by apply forget.liftObj_comp):
      forget.liftIso (f ≫ g) hX' = forget.liftIso f hX' ≫ eqToHom hY' ≫
      forget.liftIso g h' ≫ eqToHom e := by
  simp only [liftIso]
  subst hX' hY'
  simp
  simp[Groupoidal.toTransport_comp]
  simp[Groupoidal.toTransport_id]
  congr 2
  simp[← heq_eq_eq,← Category.assoc,liftObj]
  congr 1
  rw[Groupoidal.transport_congr ((X'.transport (𝟙 X'.base))) X' (by rw[Groupoidal.transport_id])
   f f (by simp)]

  rw[Groupoidal.transport_congr (X'.transport (𝟙 X'.base ≫ f)) (X'.transport f) _
   ((𝟙 (X'.transport (𝟙 X'.base ≫ f)).base)) (eqToHom (by simp))]
  · simp[Groupoidal.transport_id]
  · simp
  · simp


  -- simp[Category.assoc]
  -- simp[Groupoidal.toTransport_eqToHom]

  -- simp
  -- rw!(castMode :=.all)[Groupoidal.transport_id]
  -- rw!(castMode :=.all)[Groupoidal.transport_eqToHom]
  -- rw!(castMode :=.all)[← Category.assoc]
  -- simp[Groupoidal.toTransport_comp]
  -- congr 1
  -- congr 1
  -- --simp[Category.assoc]
  -- simp[← heq_eq_eq]
  -- simp[← Category.assoc]
  -- rw!(castMode :=.all)[Groupoidal.transport_eqToHom]

  --simp[heq_comp_eqToHom_iff] this one is autosimp
  --conv in (eqToHom sorry ≫ f ≫ g) => simp[← CategoryStruct.assoc]



def forget :
    SplitIsofibration (Groupoidal.forget (F := F)) where
      liftObj f := forget.liftObj f
      liftIso f := forget.liftIso f
      isHomLift f := forget.isHomLift f
      liftIso_IsIso f := forget.liftIso_IsIso f
      liftObj_id f := forget.liftObj_id f
      liftIso_id f := forget.liftIso_id f
      liftObj_comp {X Y Z} f _ g _ := by
       intro X' hX' Y' hY'
       apply forget.liftObj_comp
       assumption
      liftIso_comp := by
       intro X Y Z f i1 g i2 X' hX' Y' hY'
       apply forget.liftIso_comp



end



def id {A : Type u} [Category.{v} A] : SplitIsofibration (𝟭 A) :=
  iso (Functor.Iso.refl _)

section

variable {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C] {F : A ⥤ B}
         (IF : SplitIsofibration F) {G : B ⥤ C} (IG : SplitIsofibration G)


def comp.liftObj {X Y: C} (f: X ⟶ Y) [i:IsIso f] {X': A} (hX': (F ⋙ G).obj X' = X) : A
  := let f1 := IG.liftIso (X' := F.obj X') f (by simp at hX'; assumption)
     IF.liftObj (X' := X') f1 rfl


lemma comp.obj_liftObj {X Y: C} (f: X ⟶ Y) [i:IsIso f] {X': A} (hX': (F ⋙ G).obj X' = X) :
(F ⋙ G).obj (liftObj IF IG f hX') = Y := by
  simp[liftObj]

def comp.liftIso {X Y: C} (f: X ⟶ Y) [i:IsIso f] {X': A} (hX': (F ⋙ G).obj X' = X) :
  X' ⟶ comp.liftObj IF IG f hX' :=
    let f1 := IG.liftIso (X' := F.obj X') f (by simp at hX'; assumption)
    IF.liftIso (X' := X') f1 rfl

def comp.isHomLift {X Y: C} (f: X ⟶ Y) [i:IsIso f] {X': A} (hX': (F ⋙ G).obj X' = X):
 (F ⋙ G).IsHomLift f (comp.liftIso IF IG f hX') := by
  apply IsHomLift.of_fac
  · simp[comp.liftIso]
    let e := ClovenIsofibration.map_liftIso' (F := F)
    rw[e]
    simp[eqToHom_map]
    simp[ClovenIsofibration.map_liftIso']
    rw![liftObj]
    simp
  · assumption
  · simp[liftObj,ClovenIsofibration.obj_liftObj]


lemma comp.liftObj_id {X: C} {X': A} (hX': (F ⋙ G).obj X' = X):
 comp.liftObj IF IG (𝟙 X) hX' = X' := by
 simp[comp.liftObj,liftIso_id]


lemma comp.liftIso_id {X : C} {X' : A} (hX' : (F ⋙ G).obj X' = X) :
    comp.liftIso IF IG (𝟙 X) hX' = eqToHom (by simp[comp.liftObj_id]) := by
  simp [comp.liftIso]
  rw! (castMode := .all) [IG.liftIso_id]
  simp [← heq_eq_eq]
  apply HEq.trans (eqToHom_heq_id_dom _ _ _) (eqToHom_heq_id_dom _ _ _).symm


lemma comp.liftObj_comp {X Y Z : C} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [ IsIso g] {X' : A}
    (hX' : (F ⋙ G).obj X' = X):
    comp.liftObj IF IG (f ≫ g) hX' =
    comp.liftObj (X' := comp.liftObj IF IG f hX') IF IG g
    (by simp only[comp.obj_liftObj]) := by
  simp only [liftObj, liftIso_comp, eqToHom_refl, Category.id_comp, SplitIsofibration.liftObj_comp,
    liftObj_eqToHom]
  congr!
  simp[ClovenIsofibration.obj_liftObj]


lemma comp.liftIso_comp_aux {X Y Z : C} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [ IsIso g] {X' : A}
   (hX' : (F ⋙ G).obj X' = X) (Y' : A)
   (hY' : comp.liftObj IF IG f hX' = Y'): G.obj (F.obj Y') = Y := by subst hY'; simp[comp.liftObj]


lemma comp.liftIso_comp {X Y Z : C} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [ IsIso g] {X' : A}
    (hX' : (F ⋙ G).obj X' = X) (Y' : A)
    (hY' : comp.liftObj IF IG f hX' = Y'):
      comp.liftIso IF IG (f ≫ g) hX' = comp.liftIso IF IG f hX' ≫ eqToHom hY' ≫
      comp.liftIso IF IG g (by subst hY';simp[liftObj]) ≫
      eqToHom (by subst hY'; simp[comp.liftObj_comp]) := by
   simp only [liftObj, liftIso]
   have e:= @SplitIsofibration.liftIso_comp (f:= f) (g:= g) _ _ _ _ G IG X Y Z _ _ (F.obj X') hX' (IG.liftObj f hX') rfl
   rw![e,eqToHom_refl,Category.id_comp]
   simp only [SplitIsofibration.liftIso_comp, eqToHom_refl, liftIso_eqToHom, eqToHom_trans,
     Category.id_comp, Category.assoc]
   congr 1
   simp only [← heq_eq_eq, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff, comp_eqToHom_heq_iff]
   congr!
   · subst hY'
     simp[liftObj] --do not know why it works, but it did
   subst hY'
   simp[liftObj]


/-- `IsMultiplicative` 1/2 -/
def comp  :
    SplitIsofibration (F ⋙ G) where
  liftObj := comp.liftObj IF IG
  liftIso := comp.liftIso IF IG
  isHomLift := comp.isHomLift IF IG
  liftObj_id  := by
   intro X X' hX'
   apply comp.liftObj_id
  liftIso_id := by
   intro X X' hX'
   apply comp.liftIso_id
  liftObj_comp := by
   intro X Y Z f i1 g i2 X' hX' Y' hY'
   simp only [comp.liftObj_comp]
   congr
  liftIso_comp := by
   intro X Y Z f i1 g i2 X' hX' Y' hY'
   simp only [comp.liftIso_comp]
   congr!
  liftIso_IsIso := by
   intro X Y f i1 X' hX'
   simp[comp.liftIso]
   apply liftIso_IsIso


instance isoComp_SplitIsofibration {A A' B : Type u}  [Category.{v} A] [Category.{v} A']
  [Category.{v} B]
  (i : A' ≅≅ A) (F: A ⥤ B) (IF:  SplitIsofibration F): SplitIsofibration (i.hom ⋙ F) := sorry

instance iso_SplitIsofibration {A A' B : Type u}  [Category.{v} A] [Category.{v} A']
  [Category.{v} B]
  (i : A' ≅≅ A) (F: A ⥤ B) (IF:  SplitIsofibration F): SplitIsofibration (i.hom ⋙ F) := sorry

end
-- def toTerminal {A : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} A']
--     [Category.{v} B'] (top : A' ⥤ A) (F' : A' ⥤ B') (F : A ⥤ B) (bot : B' ⥤ B)
--     (isPullback : Functor.IsPullback top F' F bot) (IF : SplitIsofibration F) :
--     SplitIsofibration F' where
--   liftObj := sorry
--   liftIso := sorry
--   isHomLift := sorry
--   liftObj_id := sorry
--   liftIso_id := sorry
--   liftObj_comp := sorry
--   liftIsoComp := sorry

section
/-- `IsStableUnderBaseChange` -/

def ofIsPullback {A B A' B' : Type u} [Groupoid.{v} A] [Groupoid.{v} B] [Groupoid.{v} A']
    [Groupoid.{v} B'] (top : A' ⥤ A) (F' : A' ⥤ B') (F : A ⥤ B) (bot : B' ⥤ B)
    (isPullback : Functor.IsPullback top F' F bot) (IF : SplitIsofibration F) :
    SplitIsofibration F' := by
  --have c:= SplitIsofibration.classifier IF
  --have p : Functor.Groupoidal IF.classifier ≅≅ A := sorry
  have Ichar : SplitIsofibration (Groupoidal.forget (F := IF.classifier)) := by
    apply Functor.SplitIsofibration.forget
  have Ichar' : SplitIsofibration (Groupoidal.forget (F := bot ⋙ IF.classifier)) := by
    apply Functor.SplitIsofibration.forget
  let i0 : Functor.Groupoidal IF.classifier ≅≅ A :=
      Functor.SplitIsofibration.grothendieckClassifierIso ..
  have e0 : i0.hom ⋙ F = Groupoidal.forget := by
   simp[i0]

   sorry
  -- have p1 : Functor.IsPullback (Libya := A') (Egypt := PGrpd)
  --           (top ⋙ i0.hom ⋙ Groupoidal.toPGrpd IF.classifier)
  --           F' PGrpd.forgetToGrpd (bot ⋙ IF.classifier)
  --  := sorry
  -- have p2 : Functor.IsPullback
  --           (Groupoidal.toPGrpd (bot ⋙ IF.classifier))
  --           Groupoidal.forget PGrpd.forgetToGrpd (bot ⋙ IF.classifier)
  --  := sorry

  have q2 : Functor.IsPullback (Libya := A') (Egypt := A)
            top F' F bot
   := isPullback
  have gpb : Functor.IsPullback (Groupoidal.pre IF.classifier bot)
             Groupoidal.forget Groupoidal.forget bot := by
             apply Groupoidal.compGrothendieck.isPullback
  let d := IsPullback.IsPullback.botDegenerate e0.symm
  have paste := Functor.IsPullback.Paste.horiz sorry sorry d gpb
  simp[Functor.id_comp] at paste
  have q1 : Functor.IsPullback
            (Groupoidal.pre IF.classifier bot ⋙ i0.hom)
            (Groupoidal.forget (F := (bot ⋙ IF.classifier))) F bot
    := paste
  let j : A' ≅≅ Functor.Groupoidal (F := bot ⋙ IF.classifier) :=
     Functor.IsPullback.isoIsPullback q2 q1
  have e: F' = j.hom ⋙ (Groupoidal.forget (F := bot ⋙ IF.classifier)) := by
    symm
    have e1 := IsPullback.isoIsPullback.homCompRight' q2 q1 (hom := j.hom) (by simp[j])
    exact e1
  -- let i : A' ≅≅ Functor.Groupoidal (F := bot ⋙ IF.classifier) :=
  --    Functor.IsPullback.isoIsPullback p1 p2
  -- have eq: F' = i.hom ⋙ (Groupoidal.forget (F := bot ⋙ IF.classifier)) := by
  --   symm
  --   --simp[i]
  --   have e1 := IsPullback.isoIsPullback.homCompLeft' p1 p2 (hom := i.hom) (by simp[i])

  --   sorry
  simp[e]
  apply iso_SplitIsofibration j (Groupoidal.forget (F := bot ⋙ IF.classifier))
  exact Ichar'


end
#exit
namespace IsIsofibration

def isofibration B A : Grpd {F : B ⟶ A} (hF : IsIsofibration F) : F.Isofibration := sorry

/-- The Grothendieck construction on the classifier is isomorphic to `E`,
now as objects in `Grpd`. -/
def grothendieckClassifierIso {B A : Grpd} {F : B ⟶ A} (hF : IsIsofibration F) :
    Grpd.of (∫ hF.isofibration.classifier) ≅ B :=
  Grpd.mkIso (Functor.Isofibration.grothendieckClassifierIso ..)

-- lemma grothendieckClassifierIso_hom_comp_eq_forget {B A : Grpd} {F : B ⟶ A} (hF : IsIsofibration F) :
--     hF.grothendieckClassifierIso.hom ⋙ F = homOf Functor.Groupoidal.forget :=
--   sorry

lemma grothendieckClassifierIso_inv_comp_forget {B A : Grpd} {F : B ⟶ A} (hF : IsIsofibration F) :
    hF.grothendieckClassifierIso.inv ⋙ homOf Functor.Groupoidal.forget = F :=
  sorry

end IsIsofibration

instance : IsIsofibration.IsStableUnderBaseChange := by
  dsimp [IsIsofibration]
  infer_instance

instance : IsIsofibration.IsMultiplicative := by
  dsimp [IsIsofibration]
  infer_instance

instance : IsIsofibration.HasObjects := by
  sorry

section

attribute [local instance] Grpd.IsIsofibration.isofibration

open Functor.Isofibration

def strictify {C B A : Grpd} {F : B ⟶ A} (hF : IsIsofibration F) (G : C ⟶ B) :
    C ⟶ Grpd.of (∫ classifier (hF.isofibration)) :=
  G ≫ hF.grothendieckClassifierIso.inv

def isIsofibration_strictify {C B A : Grpd} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : IsIsofibration (strictify hF G) := sorry

def isofibration_strictify {C B A : Grpd} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : (strictify hF G).Isofibration := sorry

/-- The object part (a groupoid) of the pushforward along `F`, of `G`,
defined as the Grothendieck construction applied to (unstructured) Pi-type construction
in the HoTTLean groupoid model. -/
def pushforwardLeft {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : Grpd :=
  Grpd.of <| ∫ (GroupoidModel.FunctorOperation.pi (hF.isofibration.classifier)
    (classifier (isofibration_strictify hF hG)))

/-- The morphism part (a functor) of the pushforward along `F`, of `G`.
This is defined as the forgetful functor from the Grothendieck construction. -/
def pushforwardHom {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : pushforwardLeft hF hG ⟶ A :=
  Grpd.homOf Functor.Groupoidal.forget

/-- The pushforward along `F`, of `G`, as an object in the over category. -/
abbrev pushforward {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : Over A :=
  Over.mk (pushforwardHom hF hG)

lemma pushforward.hom {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) :
    (pushforward hF hG).hom = pushforwardHom .. := rfl

open Limits in
lemma pullback_isPullback {B A} {F : B ⟶ A} (hF : IsIsofibration F) (σ : Over A) :
    IsPullback (pullback.snd σ.hom F ≫ hF.grothendieckClassifierIso.inv) (pullback.fst σ.hom F)
    (homOf Functor.Groupoidal.forget) (homOf σ.hom) :=
  IsPullback.of_iso (IsPullback.of_hasPullback σ.hom F).flip (Iso.refl _)
    (hF.grothendieckClassifierIso ..).symm (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by
      simpa using hF.grothendieckClassifierIso_inv_comp_forget.symm )
    (by simp)

lemma pre_classifier_isPullback {B A} {F : B ⟶ A} (hF : IsIsofibration F) (σ : Over A) :
    IsPullback (homOf (pre hF.isofibration.classifier σ.hom)) (homOf Functor.Groupoidal.forget)
    (homOf Functor.Groupoidal.forget) (homOf σ.hom) := by
  have outer_pb := Functor.Groupoidal.isPullback (σ.hom ⋙ hF.isofibration.classifier)
  have right_pb := Functor.Groupoidal.isPullback (hF.isofibration.classifier)
  have left_pb := Functor.IsPullback.Paste.ofRight' outer_pb.comm_sq outer_pb right_pb.comm_sq
    right_pb (pre _ _) (by
    apply right_pb.hom_ext
    · simp [Functor.IsPullback.fac_left]
    · simp [Functor.IsPullback.fac_right, pre_comp_forget])
  exact Grpd.isPullback left_pb

/--
∫(σ ⋙ classifier) --> ∫ classifier ≅ B
      |                   |
      |                   | forget ≅ F
      |                   |
      V                   V
      Δ   ------------->  A
                  σ
The two versions of the pullback are isomorphic.
-/
def pullbackIsoGrothendieck {B A} {F : B ⟶ A} (hF : IsIsofibration F) (σ : Over A) :
    Grpd.of (∫ σ.hom ⋙ hF.isofibration.classifier) ≅ Limits.pullback σ.hom F :=
  (pre_classifier_isPullback hF σ).isoIsPullback _ _ (pullback_isPullback hF σ)

open GroupoidModel.FunctorOperation.pi in
/-- `∫ σ.hom ⋙ hF.isofibration.classifier` is the pullback of `F` along `σ`,
`∫ (isofibration_strictify hF hG).classifier` is isomorphic to `G`.
So up to isomorphism this is the hom set bijection we want. -/
def pushforwardHomEquivAux1 {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) (σ : Over A) :
    (σ ⟶ pushforward hF hG) ≃
    {f : ∫ σ.hom ⋙ hF.isofibration.classifier ⥤ ∫ (isofibration_strictify hF hG).classifier //
      f ⋙ Functor.Groupoidal.forget = pre hF.isofibration.classifier σ.hom } where
  toFun f := ⟨equivFun _ f.left f.w, equivFun_comp_forget ..⟩
  invFun f := Over.homMk (equivInv _ f.1 f.2)
    (equivInv_comp_forget ..)
  left_inv f := by
    ext
    simp [equivInv_equivFun]
  right_inv f := by
    ext
    simp [equivFun_equivInv]

def pushforwardHomEquivAux2 {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) (σ : Over A) :
    { f : ∫ σ.hom ⋙ hF.isofibration.classifier ⥤ ∫ (isofibration_strictify hF hG).classifier //
      f ⋙ Functor.Groupoidal.forget = pre hF.isofibration.classifier σ.hom } ≃
    ((Over.pullback F).obj σ ⟶ Over.mk G) where
  toFun f := Over.homMk ((pullbackIsoGrothendieck hF σ).inv ≫ Grpd.homOf f.1 ≫
    ((isIsofibration_strictify hF hG)).grothendieckClassifierIso.hom) sorry
  invFun f := ⟨(pullbackIsoGrothendieck hF σ).hom ≫ f.left ≫
    ((isIsofibration_strictify hF hG)).grothendieckClassifierIso.inv, sorry⟩
  left_inv := sorry
  right_inv := sorry

open GroupoidModel.FunctorOperation.pi in
/-- The universal property of the pushforward, expressed as a (natural) bijection of hom sets. -/
def pushforwardHomEquiv {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) (σ : Over A) :
    (σ ⟶ pushforward hF hG) ≃ ((Over.pullback F).obj σ ⟶ Over.mk G) :=
  calc (σ ⟶ pushforward hF hG)
  _ ≃ {f : ∫ σ.hom ⋙ hF.isofibration.classifier ⥤ ∫ (isofibration_strictify hF hG).classifier //
      (f ⋙ Functor.Groupoidal.forget = pre hF.isofibration.classifier σ.hom)} :=
    pushforwardHomEquivAux1 ..
  _ ≃ ((Over.pullback F).obj σ ⟶ Over.mk G) := pushforwardHomEquivAux2 ..



/-- Naturality in the universal property of the pushforward. -/
lemma pushforwardHomEquiv_comp {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G)
    {X X' : Over A} (f : X ⟶ X') (g : X' ⟶ pushforward hF hG) :
    (pushforwardHomEquiv hF hG X) (f ≫ g) =
    (Over.pullback F).map f ≫ (pushforwardHomEquiv hF hG X') g := by
  sorry


def pushforward_isPushforward  {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : IsPushforward F (Over.mk G) (pushforward hF hG) where
  homEquiv := pushforwardHomEquiv ..
  homEquiv_comp f g := pushforwardHomEquiv_comp hF hG f g

instance : IsIsofibration.HasPushforwards IsIsofibration :=
  fun F _ G => {
    has_representation := ⟨pushforward F.2 G.2, ⟨pushforward_isPushforward F.2 G.2⟩⟩ }

def isoPushforwardOfIsPushforward  {B A} {F : B ⟶ A} (hF : IsIsofibration F)
 (G: Over B) (hG : IsIsofibration G.hom) (G': Over A)
 (h: IsPushforward F G G') : G' ≅ pushforward hF hG :=
  CategoryTheory.Functor.RepresentableBy.uniqueUpToIso
  (F := (Over.pullback F).op ⋙ yoneda.obj G)
  (by simp[IsPushforward] at h; assumption)
  ({
    homEquiv := pushforwardHomEquiv ..
    homEquiv_comp f g := by apply pushforwardHomEquiv_comp ..
  } )

-- This should follow from `Groupoidal.forget` being an isofibration.
-- (If we manage to directly define the pushforward
-- as a grothendieck construction)
theorem isIsofibration_pushforward {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : IsIsofibration (pushforwardHom hF hG) :=
  sorry

-- FIXME. For some reason needed in the proof
-- `IsIsofibration.IsStableUnderPushforward IsIsofibration`
instance IsIsofibration.RespectsIso : IsIsofibration.RespectsIso := inferInstance

/-  TODO: following instance can be proven like so
  1. any pushforward is isomorphic to a chosen pushforward
     This should be proven in general for pushforwards,
     and even more generally for partial right adjoint objects) :
     `(F.op ⋙ yoneda.obj X).IsRepresentable` and
     `(F.op ⋙ yoneda.obj Y).IsRepresentable` implies
     `X ≅ Y`.
  2. Isofibrations are stable under isomorphism (this is in mathlib, for any `rlp`)
    `MorphismProperty.rlp_isMultiplicative`
    `MorphismProperty.respectsIso_of_isStableUnderComposition`
  3. The chosen pushforward is an isofibration `isIsofibration_pushforward` -/

instance : IsIsofibration.IsStableUnderPushforward IsIsofibration where
  of_isPushforward F G P := by
    intro h
    have p:  (Over.mk P) ≅ Grpd.pushforward (F.snd) (G.snd) :=
      isoPushforwardOfIsPushforward F.snd (Over.mk G.fst) G.snd (Over.mk P) h
    have i1 : IsIsofibration (pushforwardHom (F.snd) (G.snd)) := by
     apply isIsofibration_pushforward
    have e : P = (p.hom).left ≫ (pushforwardHom (F.snd) (G.snd)) := by
     have ee := Over.w p.hom
     simp at ee
     simp[ee]
    simp only[e]
    apply (IsIsofibration.RespectsIso).precomp
    assumption
