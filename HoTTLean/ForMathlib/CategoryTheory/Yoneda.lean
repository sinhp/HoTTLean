import Mathlib.CategoryTheory.Yoneda
import HoTTLean.ForMathlib.CategoryTheory.Adjunction.Basic

universe v₁ u₁ v₂ u₂ v₃ u₃

/-! Notation for the Yoneda embedding. -/

namespace CategoryTheory

notation:max "y(" Γ ")" => yoneda.obj Γ
notation:max "ym(" f ")" => yoneda.map f

open Lean PrettyPrinter in
@[app_unexpander Functor.obj]
def Functor.obj.unexpand : Unexpander
  | `($_ $F $X) =>
    if let .ident _ _ `yoneda _ := F.raw then
      `(y($X))
    else
      throw ()
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander Functor.map]
def Functor.map.unexpand : Unexpander
  | `($_ $F $X) =>
    if let .ident _ _ `yoneda _ := F.raw then
      `(ym($X))
    else
      throw ()
  | _ => throw ()

variable {C : Type u₁} [SmallCategory C] {F G : Cᵒᵖ ⥤ Type u₁}
  (app : ∀ {X : C}, (yoneda.obj X ⟶ F) → (yoneda.obj X ⟶ G))
  (naturality : ∀ {X Y : C} (f : X ⟶ Y) (α : yoneda.obj Y ⟶ F),
    app (yoneda.map f ≫ α) = yoneda.map f ≫ app α)

variable (F) in

/--
  A presheaf `F` on a small category `C` is isomorphic to
  the hom-presheaf `Hom(y(•),F)`.
-/
def yonedaIso : yoneda.op ⋙ yoneda.obj F ≅ F :=
  NatIso.ofComponents (fun _ => Equiv.toIso yonedaEquiv)
    (fun f => by ext : 1; dsimp; rw [yonedaEquiv_naturality'])

/-- Build natural transformations between presheaves on a small category
  by defining their action when precomposing by a morphism with
  representable domain -/
def NatTrans.yonedaMk : F ⟶ G :=
  (yonedaIso F).inv ≫ .mk (fun _ => by exact app) ≫ (yonedaIso G).hom

@[deprecated (since := "2025-11-20")] alias yonedaIsoMap := NatTrans.yonedaMk

theorem NatTrans.yonedaMk_app {X : C} (α : yoneda.obj X ⟶ F) :
    α ≫ yonedaMk app naturality = app α := by
  rw [← yonedaEquiv.apply_eq_iff_eq, yonedaEquiv_comp]
  simp [yonedaMk, yonedaIso]

example : yoneda.op ⋙ y(F) ≅ F := curriedYonedaLemma'.app F

example {D : Type*} [Category D] (S : D ⥤ Cᵒᵖ ⥤ Type u₁) :=
    S.isoWhiskerLeft curriedYonedaLemma'

def NatIso.yonedaMk (α : yoneda.op ⋙ y(F) ≅ yoneda.op ⋙ y(G)) : F ≅ G :=
  (curriedYonedaLemma'.app F).symm ≪≫ α ≪≫ curriedYonedaLemma'.app G

def NatIso.yonedaMk' (app : ∀ {X : C}, (yoneda.obj X ⟶ F) ≃ (yoneda.obj X ⟶ G))
    (naturality : ∀ {X Y : C} (f : X ⟶ Y) (α : yoneda.obj Y ⟶ F),
      app (yoneda.map f ≫ α) = yoneda.map f ≫ app α) : F ≅ G :=
  (yonedaIso F).symm ≪≫ NatIso.ofComponents (fun A => by exact Equiv.toIso app) ≪≫ (yonedaIso G)

/-- To show that `S ≅ T : D ⥤ Psh C` it suffices to prove the bijection
  `Psh C (y(c), S d) ≅ Psh C (y(c), T d)`,
  natural in both `c : Cᵒᵖ` and `d : D`. -/
def functorToPresheafIsoMk {D : Type*} [Category D] {S T : D ⥤ Cᵒᵖ ⥤ Type u₁}
    (α : S ⋙ yoneda ⋙ (Functor.whiskeringLeft Cᵒᵖ (Cᵒᵖ ⥤ Type u₁)ᵒᵖ (Type u₁)).obj yoneda.op ≅
      T ⋙ yoneda ⋙ (Functor.whiskeringLeft Cᵒᵖ (Cᵒᵖ ⥤ Type u₁)ᵒᵖ (Type u₁)).obj yoneda.op) :
    S ≅ T :=
  (S.isoWhiskerLeft curriedYonedaLemma').symm ≪≫ α ≪≫ T.isoWhiskerLeft curriedYonedaLemma'

namespace Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]

def yonedaCompCongrLeftInverseIso (e : C ≌ D) : yoneda ⋙ (congrLeft e.op).inverse ≅
    e.inverse ⋙ yoneda :=
  NatIso.ofComponents
  (fun _ => NatIso.ofComponents
    (fun _ => Equiv.toIso (e.toAdjunction.homEquiv _ _))
    (fun _ => by ext; simp [Adjunction.homEquiv_naturality_left]))
  (fun _ => by ext; simp [Adjunction.homEquiv_naturality_right])

def yonedaCompCongrLeftFunctorIso (e : C ≌ D) : yoneda ⋙ (congrLeft e.op).functor ≅
    e.functor ⋙ yoneda :=
  e.symm.yonedaCompCongrLeftInverseIso

end Equivalence

end CategoryTheory
