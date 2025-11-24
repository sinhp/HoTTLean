import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Yoneda

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor
namespace FullyFaithful

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]

variable {F : C ⥤ D} (hF : F.FullyFaithful)

def homIso : yoneda ≅ F ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F.op :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => hF.homEquiv.toIso))
