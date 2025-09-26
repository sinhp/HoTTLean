import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import HoTTLean.ForMathlib.CategoryTheory.Grpd
import HoTTLean.ForMathlib.CategoryTheory.FreeGroupoid

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory
namespace Grpd

instance : Grpd.IsIsofibration.IsStableUnderBaseChange := by
  dsimp [IsIsofibration]
  infer_instance

instance : Grpd.IsIsofibration.HasObjects := by
  sorry

instance : Grpd.IsIsofibration.IsMultiplicative := by
  dsimp [IsIsofibration]
  infer_instance

instance : Grpd.IsIsofibration.HasPushforwards Grpd.IsIsofibration :=
  sorry

instance : Grpd.IsIsofibration.IsStableUnderPushforward Grpd.IsIsofibration :=
  sorry
