import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.MorphismProperty.Basic

namespace CategoryTheory

-- Mathlib now provides this theorem. Check the original interface here.
open MorphismProperty in
example (C : Type*) [Category C] :
    IsGroupoid C ↔ isomorphisms C = ⊤ :=
  isGroupoid_iff_isomorphisms_eq_top C

end CategoryTheory
