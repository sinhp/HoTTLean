import HoTTLean.ForMathlib.Tactic.CategoryTheory.FunctorMap

/-!
# Tests for `functor_map`

Check the generated declarations, nested attributes, and term elaborator with independent
object and morphism universes in the source and target categories.
-/

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.FunctorMapTest

variable {C : Type u₁} [Category.{v₁} C]

@[functor_map (attr := reassoc (attr := simp))]
theorem comp_id_of_eq {X Y : C} (f g : X ⟶ Y) (h : f = g) : f ≫ 𝟙 Y = g := by
  simpa using h

run_cmd do
  let env ← Lean.getEnv
  for name in [``comp_id_of_eq_functor_map, ``comp_id_of_eq_functor_map_assoc] do
    unless (Lean.Meta.simpExtension.getState env).lemmaNames.contains (.decl name) do
      throwError "missing simp attribute on {name}"

variable {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

example {X Y : C} (f g : X ⟶ Y) (h : f = g) : F.map f = F.map g :=
  comp_id_of_eq_functor_map f g h F

example {X Y : C} (f g : X ⟶ Y) (h : f = g) {Z : D} (k : F.obj Y ⟶ Z) :
    F.map f ≫ k = F.map g ≫ k :=
  comp_id_of_eq_functor_map_assoc f g h F k

example {X Y : C} (f g : X ⟶ Y) (h : f = g) : F.map f = F.map g :=
  (functor_map_of% (comp_id_of_eq f g h)) F

end CategoryTheory.FunctorMapTest
