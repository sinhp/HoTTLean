/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Emily Riehl, Joseph Hua
-/
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Beck-Chevalley natural transformations and natural isomorphisms

We construct the so-called Beck-Chevalley natural transformations and isomorphisms through the
repeated applications of the mate construction in the vertical and horizontal directions.

## Main declarations

- `Over.mapIsoSquare`: The isomorphism between the functors `Over.map h ⋙ Over.map g` and
  `Over.map f ⋙ Over.map k` for a commutative square of morphisms `h ≫ g = f ≫ k`.

- `Over.pullbackMapTwoSquare`: The Beck-Chevalley natural transformation of a commutative
  square of morphisms `h ≫ g = f ≫ k`.

- `Over.pullbackForgetTriangle`: The natural transformation `pullback f ⋙ forget X ⟶ forget Y`.

- `Over.pullbackIsoSquare`: The isomorphism between the pullbacks along a commutative square of
  morphisms `h ≫ g = f ≫ k`.

- `Over.pushforwardBeckChevalleySquare`: The Beck-Chevalley natural transformation for a commutative
  square of morphisms `h ≫ g = f ≫ k` in the slice category `Over Y`.

- `Over.pushforwardSquareIso`: The isomorphism between the pushforwards along a commutative
  square of morphisms `h ≫ g = f ≫ k`.

## Implementation notes
The lax naturality squares are constructed by the mate equivalence `mateEquiv` and
the natural iso-squares are constructed by the more special conjugation equivalence
`conjugateIsoEquiv`.

## References

The methodology and the notation of the successive mate constructions to obtain the Beck-Chevalley
natural transformations and isomorphisms are based on the following paper:

* [A 2-categorical proof of Frobenius for fibrations defined from a generic point,
in Mathematical Structures in Computer Science, 2024][Hazratpour_Riehl_2024]

-/

noncomputable section
namespace CategoryTheory

open Category Functor Adjunction Limits NatTrans

universe v u

namespace Over

variable {C : Type u} [Category.{v} C]

section BeckChevalleyTrans

--h ≫ g = f ≫ k -- h → k
theorem map_square_eq {X Y Z W : C} {h : X ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ W} {k : Y ⟶ W}
    (sq : CommSq h f g k := by aesop) :
    Over.map h ⋙ Over.map g = Over.map f ⋙ Over.map k := by
  rw [← mapComp_eq, sq.w, mapComp_eq]

/-- Promoting the equality `mapSquare_eq` of functors to an isomorphism.
```
        Over X -- .map h -> Over Z
           |                  |
   .map f  |         ≅        | .map g
           ↓                  ↓
        Over Y -- .map k -> Over W
```
The Beck Chevalley transformations are iterated mates of this isomorphism in the
horizontal and vertical directions. -/
def mapIsoSquare {X Y Z W : C} {h : X ⟶ Z} {f : X ⟶ Y}  {g : Z ⟶ W} {k : Y ⟶ W}
    (sq : CommSq h f g k := by aesop) :
    Over.map h ⋙ Over.map g ≅ Over.map f ⋙ Over.map k :=
  eqToIso (map_square_eq sq)

variable {X Y Z W : C} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W)
  (sq : CommSq h f g k)
  [∀ {P : C} (h : P ⟶ Y), HasPullback h f]
  [∀ {P : C} (h : P ⟶ W), HasPullback h g]
  [∀ {P : C} (h : P ⟶ W), HasPullback h k]
  [∀ {P : C} (h' : P ⟶ Z), HasPullback h' h]

/-- The Beck-Chevalley natural transformation `pullback f ⋙ map h ⟶ map k ⋙ pullback g`
constructed as a mate of `mapIsoSquare`:
```
    Over Y - pullback f → Over X
      |                     |
map k |          ↙          | map h
      ↓                     ↓
    Over W - pullback g → Over Z
```
-/
--pullbackBeckChevalleySquare
def pullbackMapTwoSquare : TwoSquare (pullback f) (map k) (map h) (pullback g) :=
  mateEquiv (mapPullbackAdj f) (mapPullbackAdj g) (mapIsoSquare sq).hom

/--
The natural transformation `pullback f ⋙ forget X ⟶ forget Y ⋙ 𝟭 C`
as the mate of the isomorphism `mapForget f`:
```
       Over Y - pullback f → Over X
         |                     |
forget Y |          ↙          | forget X
         ↓                     ↓
         C ======== 𝟭 ======== C
```
-/
def pullbackForgetTwoSquare : TwoSquare (pullback f) (forget Y) (forget X) (𝟭 C) :=
  mateEquiv (mapPullbackAdj f) Adjunction.id (mapForget f).inv

-- theorem isCartesian_pullbackForgetTwoSquare {X Y : C} (f : X ⟶ Y) :
--     NatTrans.IsCartesian (pullbackForgetTwoSquare f) := by
--   unfold pullbackForgetTwoSquare
--   simp only [mateEquiv_apply]
--   repeat apply IsCartesian.comp; apply isCartesian_of_isIso
--   apply IsCartesian.comp
--   . apply IsCartesian.whiskerRight
--     apply isCartesian_mapPullbackAdj_counit
--   . apply isCartesian_of_isIso

/-- The natural transformation `pullback f ⋙ forget X ⟶ forget Y`, a variant of
`pullbackForgetTwoSquare`. -/
--pullbackForgetBeckChevalleyTriangle
def pullbackForgetTriangle :
    pullback f ⋙ forget X ⟶ forget Y :=
  pullbackForgetTwoSquare f

/-- The natural transformation `pullback f ⋙ map h ⟶ map h'` for a triangle `f : h ⟶ h'`. -/
--pullbackMapBeckChevalleyTriangle
def pullbackMapTriangle (h' : Y ⟶ Z) (w : f ≫ h' = h) :
    pullback f ⋙ map h ⟶ map h' := by
  let iso := (mapComp f h').hom
  rw [w] at iso
  rw [← Functor.comp_id (map h)] at iso
  exact (mateEquiv (mapPullbackAdj f) Adjunction.id) iso

/-- The isomorphism between the pullbacks along a commutative square.  This is constructed as the
conjugate of the `mapIsoSquare`.
```
          Over X ←--.pullback h-- Over Z
             ↑                       ↑
.pullback f  |          ≅            | .pullback g
             |                       |
          Over Y ←--.pullback k-- Over W
```
-/
--pullbackSquareIso
def pullbackIsoSquare : pullback k ⋙ pullback f ≅ pullback g ⋙ pullback h :=
  conjugateIsoEquiv ((mapPullbackAdj f).comp (mapPullbackAdj k))
  ((mapPullbackAdj h).comp (mapPullbackAdj g)) (mapIsoSquare sq)

end BeckChevalleyTrans
end Over

variable {T : Type u} [Category.{v} T] {R : MorphismProperty T}
  [R.HasPullbacks] [R.IsStableUnderBaseChange]
  {Q : MorphismProperty T} [Q.HasPullbacks] [R.HasPushforwards Q]
  [R.IsStableUnderPushforward Q]
  [R.IsStableUnderComposition]
  {X Y Z W : T} (h : X ⟶ Z) (f : X ⟶(Q) Y) (g : Z ⟶(Q) W) (k : Y ⟶ W)
  (sq : CommSq h f.1 g.1 k)

instance : MorphismProperty.HasOfPostcompProperty (C := T) ⊤ ⊤ where
  of_postcomp := sorry

/-- The Beck-Chevalley natural transformation
`pushforward g ⋙ pullback k ⟶ pullback h ⋙ pushforward f` constructed as a mate of
`pullbackMapTwoSquare`.
```
      R.Over ⊤ Z - pushforward g → R.Over ⊤ W
           |                           |
pullback h |           ↙              | pullback k
           V                           V
      R.Over ⊤ X - pushforward f → R.Over ⊤ Y
```
-/
--pushforwardBeckChevalleySquare
def pushforwardPullbackTwoSquare :
    TwoSquare (MorphismProperty.pushforward (P := R) (Q := Q) g)
    (MorphismProperty.Over.pullback R ⊤ h)
    (MorphismProperty.Over.pullback R ⊤ k)
    (MorphismProperty.pushforward (P := R) (Q := Q) f) :=
  mateEquiv (MorphismProperty.pullbackPushforwardAdjunction R Q g)
  (MorphismProperty.pullbackPushforwardAdjunction R Q f)
  ((MorphismProperty.Over.pullbackComp _ _).inv ≫
  eqToHom (by rw! [sq.w]) ≫
  (MorphismProperty.Over.pullbackComp _ _).hom)
  -- conjugateEquiv (mapPullbackAdj k |>.comp <| MorphismProperty.pullbackPushforwardAdjunction g)
  -- (MorphismProperty.pullbackPushforwardAdjunction R Q f |>.comp <|
  --   MorphismProperty.Over.mapPullbackAdj R ⊤ h)
  --   (Over.pullbackMapTwoSquare h f.1 g.1 k sq)

-- /--
-- A variant of `pushforwardTwoSquare` involving `star` instead of `pullback`.
-- -/
-- --pushforwardStarBeckChevalleySquare
-- def starPushforwardTriangle [HasBinaryProducts C] [ExponentiableMorphism f]  :
--     star Y ⟶ star X ⋙ pushforward f := by
--   let iso := (starPullbackIsoStar f).hom
--   rw [← Functor.id_comp (star X)] at iso
--   exact (mateEquiv Adjunction.id (adj f)) iso

-- /-- The conjugate isomorphism between the pushforwards along a commutative square.
-- ```
--             Over X --.pushforward h -→ Over Z
--                |                        |
-- .pushforward f |           ≅            | .pushforward g
--                ↓                        ↓
--             Over Y --.pushforward k -→ Over W
-- ```
-- -/
-- def pushforwardIsoSquare [ExponentiableMorphism f] [ExponentiableMorphism g]
--     [ExponentiableMorphism h] [ExponentiableMorphism k] :
--     pushforward h ⋙ pushforward g ≅ pushforward f ⋙ pushforward k :=
--   conjugateIsoEquiv (adj g |>.comp <| adj h) (adj k |>.comp <| adj f) (pullbackIsoSquare h f g k sq)

-- end BeckChevalleyTrans

-- end Over

-- section BeckChevalleyComponents

-- variable {C : Type u} [Category.{v} C]

-- namespace IsPullback

-- /--
-- In a commutative cube diagram if the front, back and the right face are pullback squares then
-- the the left face is also a pullback square.
-- ```
--           P ---p₂------  X
--          /|             /|
--     i₄  / |       i₂   / |
--        /  |           /  | f₂
--       Q ----q₂-----  Z   |
--       |   |          |   |
--       |   W -f₁----- | - S
--   q₁  |  /           |  /
--       | / i₁         | / i₃
--       |/             |/
--       Y ----g₁------ T
-- ```
-- -/
-- theorem left_face_of_comm_cube {P W X Y Q Z S T : C}
--     (p₁ : P ⟶ W) (p₂ : P ⟶ X) (f₁ : W ⟶ S) (f₂ : X ⟶ S)
--     (q₁ : Q ⟶ Y) (q₂ : Q ⟶ Z) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T)
--     (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (i₄ : P ⟶ Q)
--     (sq_top : CommSq p₂ i₄ i₂ q₂)
--     (sq_bot : CommSq f₁ i₁ i₃ g₁)
--     (sq_left : CommSq i₄ p₁ q₁ i₁)
--     (pb_back : IsPullback p₂ p₁ f₂ f₁)
--     (pb_front : IsPullback q₂ q₁ g₂ g₁)
--     (pb_right : IsPullback i₂ f₂ g₂ i₃) :
--     IsPullback i₄ p₁ q₁ i₁ := by
--   have paste_horiz_pb := paste_horiz pb_back pb_right
--   rw [sq_top.w, sq_bot.w] at paste_horiz_pb
--   exact of_right paste_horiz_pb sq_left.w pb_front

-- /--
-- In a commutative cube diagram if the front, the left and the right face are pullback squares then
-- the the back face is also a pullback square.
-- ```
--           P ---p₂------  X
--          /|             /|
--     i₄  / |       i₂   / |
--        /  |           /  | f₂
--       Q ----q₂-----  Z   |
--       |   |          |   |
--       |   W -f₁----- | - S
--   q₁  |  /           |  /
--       | / i₁         | / i₃
--       |/             |/
--       Y ----g₁------ T
-- ```
-- -/
-- theorem back_face_of_comm_cube {P W X Y Q Z S T : C}
--     (p₁ : P ⟶ W) (p₂ : P ⟶ X) (f₁ : W ⟶ S) (f₂ : X ⟶ S)
--     (q₁ : Q ⟶ Y) (q₂ : Q ⟶ Z) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T)
--     (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (i₄ : P ⟶ Q)
--     (sq_top : CommSq p₂ i₄ i₂ q₂)
--     (sq_bot : CommSq f₁ i₁ i₃ g₁)
--     (sq_back : CommSq p₂ p₁ f₂ f₁)
--     (pb_front : IsPullback q₂ q₁ g₂ g₁)
--     (pb_left : IsPullback i₄ p₁ q₁ i₁)
--     (pb_right : IsPullback i₂ f₂ g₂ i₃) :
--     IsPullback p₂ p₁ f₂ f₁ := by
--   have paste_horiz_pb := paste_horiz pb_left pb_front
--   rw [← sq_top.w, ← sq_bot.w] at paste_horiz_pb
--   exact of_right paste_horiz_pb sq_back.w pb_right

-- /-- The pullback comparison map `pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃` between two
-- pullback squares is an isomorphism if  `i₁` is an isomorphism and one of the
-- connecting morphisms is an isomorphism. -/
-- theorem pullback.map_isIso_of_pullback_right_of_comm_cube {W X Y Z S T : C}
--     (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
--     (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂]
--     (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
--     (sq_bot : CommSq f₁ i₁ i₃ g₁)
--     [IsIso i₁] (pb_right : IsPullback i₂ f₂ g₂ i₃) :
--     IsIso (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ sq_bot.w pb_right.w.symm) := by
--   let m := pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ sq_bot.w pb_right.w.symm
--   have sq_top : CommSq (pullback.snd f₁ f₂) m i₂ (pullback.snd g₁ g₂) := by
--     aesop
--   have sq_left : CommSq m (pullback.fst f₁ f₂) (pullback.fst g₁ g₂) i₁ := by
--     aesop
--   let pb' : IsPullback m (pullback.fst f₁ f₂)  (pullback.fst g₁ g₂) i₁ := by
--     apply IsPullback.left_face_of_comm_cube (sq_top := sq_top) (sq_bot := sq_bot)
--       (sq_left := sq_left) (pb_back := (IsPullback.of_hasPullback f₁ f₂).flip)
--       (pb_front := (IsPullback.of_hasPullback g₁ g₂).flip)
--       (pb_right := pb_right)
--   have is_iso : IsIso m := IsPullback.isIso_fst_of_isIso pb'
--   exact is_iso

-- end IsPullback

-- variable [HasPullbacks C]

-- variable {X Y Z W : C} {h : X ⟶ Z} {f : X ⟶ Y}  {g : Z ⟶ W} {k : Y ⟶ W}
-- (sq : CommSq h f g k) (A : Over Y)

-- open IsPullback Over

-- theorem mapPullbackAdj.counit_app_left  :
--     ((mapPullbackAdj f).counit.app A).left = pullback.fst _ _ := by
--   simp only [mapPullbackAdj_counit_app, homMk_left]

-- @[simp]
-- theorem pullbackMapTwoSquare_app :
--     (pullbackMapTwoSquare h f g k sq).app A =
--     Over.homMk (pullback.map _ _ (A.hom ≫ k) _ _ h k (id_comp _).symm sq.w.symm) (by aesop) := by
--   ext
--   simp only [homMk_left, pullbackMapTwoSquare, mapIsoSquare]
--   aesop

-- theorem forget_map_pullbackMapTwoSquare :
--     (forget Z).map ((pullbackMapTwoSquare h f g k sq).app A) =
--     pullback.map _ _ _ _ (𝟙 _) h k (id_comp _).symm sq.w.symm := by
--   simp only [forget_map, pullbackMapTwoSquare_app, homMk_left]

-- theorem isIso_forgetMappullbackMapTwoSquare_of_isPullback (pb : IsPullback h f g k) :
--     IsIso ((forget Z).map ((pullbackMapTwoSquare h f g k pb.toCommSq).app A)) := by
--   rw [forget_map_pullbackMapTwoSquare (sq:= pb.toCommSq)]
--   let paste_horiz_pb := paste_horiz (IsPullback.of_hasPullback f A.hom) pb
--   apply pullback.map_isIso_of_pullback_right_of_comm_cube
--   assumption'
--   aesop

-- /-- The pullback Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
-- instance pullbackMapTwoSquare_of_isPullback_isIso (pb : IsPullback h f g k) :
--     IsIso (pullbackMapTwoSquare h f g k pb.toCommSq) := by
--   apply (config := { allowSynthFailures:= true}) NatIso.isIso_of_isIso_app
--   intro A
--   have := isIso_forgetMappullbackMapTwoSquare_of_isPullback A pb
--   exact ReflectsIsomorphisms.reflects (forget Z)
--     ((pullbackMapTwoSquare h f g k pb.toCommSq).app A)

-- /-- The pullback-map exchange isomorphism. -/
-- def pullbackMapIsoSquare (pb : IsPullback h f g k) :
--     pullback f ⋙ map h ≅ Over.map k ⋙ Over.pullback g := by
--   refine @asIso _ _ _ _ (pullbackMapTwoSquare h f g k pb.toCommSq) ?_
--   exact pullbackMapTwoSquare_of_isPullback_isIso pb

-- /-- The functor Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
-- instance pushforwardPullbackTwoSquare_of_isPullback_isIso (pb : IsPullback h f g k)
--     [ExponentiableMorphism f] [ExponentiableMorphism g] :
--     IsIso (pushforwardPullbackTwoSquare h f g k pb.toCommSq) := by
--   have := pullbackMapTwoSquare_of_isPullback_isIso pb
--   apply conjugateEquiv_iso

-- /-- The pullback-pushforward exchange isomorphism. -/
-- def pushforwardPullbackIsoSquare (pb : IsPullback h f g k)
--     [ExponentiableMorphism f] [ExponentiableMorphism g] :
--     pushforward g ⋙ pullback k ≅ pullback h ⋙ pushforward f := by
--   refine @asIso _ _ _ _ (pushforwardPullbackTwoSquare h f g k pb.toCommSq) ?_
--   exact pushforwardPullbackTwoSquare_of_isPullback_isIso pb

-- end BeckChevalleyComponents

-- end CategoryTheory

-- end
