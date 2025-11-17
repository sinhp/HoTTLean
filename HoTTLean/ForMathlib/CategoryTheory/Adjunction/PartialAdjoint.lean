import Mathlib.CategoryTheory.Adjunction.PartialAdjoint


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

open Category Opposite Limits

section PartialRightAdjoint

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

structure PartialRightAdjoint (G : F.PartialRightAdjointSource ⥤ C) where
  (repr : ∀ Y, (F.op ⋙ yoneda.obj Y.obj).RepresentableBy (G.obj Y))
  (repr_homEquiv : ∀ X Y (f : X ⟶ Y), (repr Y).homEquiv (G.map f) =
    (repr X).homEquiv (𝟙 _) ≫ f)

@[simps]
noncomputable def partialRightAdjoint.partialRightAdjoint :
    PartialRightAdjoint F (partialRightAdjoint F) where
  repr _ := Functor.representableBy _
  repr_homEquiv _ _ _ := by
    simp only [partialRightAdjoint_obj, comp_obj, op_obj, yoneda_obj_obj, partialRightAdjoint_map,
      partialRightAdjointMap, partialRightAdjointHomEquiv]
    erw [Equiv.apply_symm_apply]

@[simps]
noncomputable def rightAdjoint.partialRightAdjoint (L : C ⥤ D) [IsLeftAdjoint L] :
    PartialRightAdjoint L (ObjectProperty.ι _ ⋙ rightAdjoint L) where
  repr Y := Adjunction.representableBy (Adjunction.ofIsLeftAdjoint L) _
  repr_homEquiv a b c := by
    simp [Equiv.symm_apply_eq, Adjunction.homEquiv_naturality_right]

lemma PartialRightAdjoint.repr_homEquiv_comp {G : F.PartialRightAdjointSource ⥤ C}
    (P : PartialRightAdjoint F G) {X Y Z} (f : X ⟶ Y) (a : Z ⟶ G.obj X) :
    (P.repr Y).homEquiv (a ≫ G.map f) = (P.repr X).homEquiv a ≫ f := by
  have := (P.repr X).homEquiv_comp a (𝟙 _)
  rw [(P.repr Y).homEquiv_comp, P.repr_homEquiv]
  cat_disch

lemma PartialRightAdjoint.repr_homEquiv_symm_comp {G : F.PartialRightAdjointSource ⥤ C}
    (P : PartialRightAdjoint F G) {X Y Z} (f : X ⟶ Y) (a : F.obj Z ⟶ X.obj) :
    (P.repr Y).homEquiv.symm (a ≫ f) = (P.repr X).homEquiv.symm a ≫ G.map f := by
  rw [Equiv.symm_apply_eq, repr_homEquiv_comp, Equiv.apply_symm_apply]

def PartialRightAdjoint.uniqueUpToIso {G G' : F.PartialRightAdjointSource ⥤ C}
    (P : PartialRightAdjoint F G) (P' : PartialRightAdjoint F G') : G ≅ G' :=
  NatIso.ofComponents (fun X => (P.repr _).uniqueUpToIso (P'.repr _))
  (fun {X Y} f => by
    apply yoneda.map_injective
    ext Z a
    simp only [yoneda_obj_obj, RepresentableBy.uniqueUpToIso_hom, comp_obj, op_obj, map_comp,
      FullyFaithful.map_preimage, FunctorToTypes.comp, yoneda_map_app, NatIso.ofComponents_hom_app,
      Function.comp_apply]
    calc (P'.repr Y).homEquiv.symm ((P.repr Y).homEquiv (a ≫ G.map f))
    _ = (P'.repr Y).homEquiv.symm ((P.repr X).homEquiv a ≫ f) := by
      simpa using PartialRightAdjoint.repr_homEquiv_comp ..
    _ = (P'.repr X).homEquiv.symm ((P.repr X).homEquiv a) ≫ G'.map f := by
      apply repr_homEquiv_symm_comp)

noncomputable abbrev isoPartialRightAdjoint (G : F.PartialRightAdjointSource ⥤ C)
    (P : PartialRightAdjoint F G) : G ≅ partialRightAdjoint F :=
    PartialRightAdjoint.uniqueUpToIso _ P (partialRightAdjoint.partialRightAdjoint _)
