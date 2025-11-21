import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Mathlib.Tactic.DepRewrite

namespace CategoryTheory

open Category Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {A : C}


-- def CostructuredArrowYonedaOver :
--     CostructuredArrow yoneda (yoneda.obj (A)) ≅ CategoryTheory.Over A where
--   hom X := Over.mk ((CategoryTheory.Yoneda.fullyFaithful).preimage X.hom)
--   inv X := CostructuredArrow.mk (yoneda.map X.hom)

def CostructuredArrowYonedaOver_functor : CostructuredArrow yoneda (yoneda.obj A) ⥤ Over A where
  obj X := Over.mk ((CategoryTheory.Yoneda.fullyFaithful).preimage X.hom)
  map {X Y} f := by
   have w := f.w
   have e:
    (yoneda.map f.left ≫ Y.hom).app (op X.left) =
    (X.hom ≫ (Functor.fromPUnit (yoneda.obj A)).map f.right).app (op X.left) := by
    simp[w]
   simp[- CommaMorphism.w] at e
   apply Over.homMk f.left (by simp[CategoryTheory.Yoneda.fullyFaithful_preimage,← e])



def CostructuredArrowYonedaOver_inverse : Over A ⥤ CostructuredArrow yoneda (yoneda.obj A) where
  obj X := CostructuredArrow.mk (yoneda.map X.hom)
  map {X Y} f := CostructuredArrow.homMk f.left

lemma CostructuredArrowYonedaOver_inverse_functor :
  CostructuredArrowYonedaOver_inverse (A := A) ⋙ CostructuredArrowYonedaOver_functor = Functor.id _
 := sorry



lemma CostructuredArrowYonedaOver_functor_inverse :
  CostructuredArrowYonedaOver_functor ⋙ CostructuredArrowYonedaOver_inverse (A := A) = Functor.id _
 := sorry

def CostructuredArrowYonedaOver_unitIso :
  𝟭 (CostructuredArrow yoneda (yoneda.obj A)) ≅
  CostructuredArrowYonedaOver_functor ⋙ CostructuredArrowYonedaOver_inverse :=
  eqToIso CostructuredArrowYonedaOver_functor_inverse.symm

def CostructuredArrowYonedaOver_unitIso1 :
  𝟭 (CostructuredArrow yoneda (yoneda.obj A)) ≅
  CostructuredArrowYonedaOver_functor ⋙ CostructuredArrowYonedaOver_inverse
  where
    hom := {
      app X := by
        dsimp
        simp[CostructuredArrowYonedaOver_inverse,CostructuredArrowYonedaOver_functor]
        exact (𝟙 _)
      naturality := by
       intro X Y f
       rw! (castMode :=.all)[CostructuredArrowYonedaOver_functor_inverse]

       sorry
    }
    inv := {
      app X := by
        dsimp
        simp[CostructuredArrowYonedaOver_inverse,CostructuredArrowYonedaOver_functor]
        exact (𝟙 _)
      naturality := sorry
    }

#check NatIso.ofComponents
#check Iso.refl

#check Over.isoMk
#check eqToIso

def CostructuredArrowYonedaOver_counitIso :
  CostructuredArrowYonedaOver_inverse ⋙ CostructuredArrowYonedaOver_functor (A:= A)
  ≅ 𝟭 _ := eqToIso CostructuredArrowYonedaOver_inverse_functor

-- def CostructuredArrowYonedaOver_counitIso1 :
--   CostructuredArrowYonedaOver_inverse ⋙ CostructuredArrowYonedaOver_functor (A:= A)
--   ≅ 𝟭 _
--   where
--     hom := {
--       app X := by
--         dsimp
--         simp[CostructuredArrowYonedaOver_inverse,CostructuredArrowYonedaOver_functor]
--         exact (𝟙 _)
--       naturality := by
--        intro X Y f
--        rw! (castMode := .all)[CostructuredArrowYonedaOver_inverse_functor]
--        simp only[CostructuredArrowYonedaOver_inverse_functor]
--        sorry
--     }
--     inv := {
--       app X := by
--         dsimp
--         simp[CostructuredArrowYonedaOver_inverse,CostructuredArrowYonedaOver_functor]
--         exact (𝟙 _)
--       naturality := sorry
--     }


-- section
-- universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆
-- variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
--    (S : C ⥤ D) (T : D) (X : CostructuredArrow S T)
-- lemma cast_left {Ty : Type _ }(e: CostructuredArrow S T = Ty):
--   (cast e (𝟙 X)).left = cast _ (𝟙 X).left  := sorry



-- end

#check NatIso.ofComponents

-- def CostructuredArrowYonedaOver1 :
--     CostructuredArrow yoneda (yoneda.obj (A)) ≌ CategoryTheory.Over A := by

--     apply NatIso.ofComponents sorry sorry


def CostructuredArrowYonedaOver :
    CostructuredArrow yoneda (yoneda.obj (A)) ≌ CategoryTheory.Over A where
      functor := CostructuredArrowYonedaOver_functor
      inverse := CostructuredArrowYonedaOver_inverse
      unitIso := CostructuredArrowYonedaOver_unitIso
      counitIso := CostructuredArrowYonedaOver_counitIso
      functor_unitIso_comp X := by
       simp[CostructuredArrowYonedaOver_functor,CostructuredArrowYonedaOver_unitIso,
            CostructuredArrowYonedaOver_counitIso]
       ext

      --  have e: (CostructuredArrow.mk (Yoneda.fullyFaithful.preimage X.hom)
      --           : CostructuredArrow (𝟭 C) A) = yoneda.map X.hom:= sorry
       simp[Over.mk]




#check overEquivPresheafCostructuredArrow
#check CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow

def PresheafCostructuredArrowYonedaOver_aux:
 (CostructuredArrow yoneda (yoneda.obj (A)))ᵒᵖ ⥤ Type v ≌
 (CategoryTheory.Over A)ᵒᵖ ⥤ Type v := by
 apply Equivalence.congrLeft
 apply CategoryTheory.Equivalence.op
 exact CostructuredArrowYonedaOver


 /-
 @CostructuredArrow C inst✝ (Cᵒᵖ ⥤ Type v) Functor.category yoneda (yoneda.obj A) : Type (max u v)
 @CostructuredArrow C inst✝ (Cᵒᵖ ⥤ Type v) Functor.category yoneda (yoneda.obj A) : Type (max u v)

 @Over C inst✝ A : Type (max u v)
 @Over C inst✝ A : Type (max u v)
 -/

--CategoryTheory.NatIso.op

def PresheafCostructuredArrowYonedaOver :
    CategoryTheory.Over (yoneda.obj (A)) ≌
    ((CategoryTheory.Over A)ᵒᵖ ⥤ Type v) :=
   Equivalence.trans (overEquivPresheafCostructuredArrow (yoneda.obj (A)))
   (PresheafCostructuredArrowYonedaOver_aux)
   -- need A equiv B -> A => Type equiv B => Type
   -- need A equiv B -> Aᵒᵖ equiv Bᵒᵖ





end CategoryTheory
