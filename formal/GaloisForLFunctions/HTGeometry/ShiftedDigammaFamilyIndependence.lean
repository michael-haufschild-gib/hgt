import GaloisForLFunctions.HTGeometry.ShiftedDigammaFamilyIncrement
import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbit

/-!
# Differential independence of a family of shifted digammas

An element whose complete jet family translates by rational increments under the unit shift is
algebraically independent from the base once no nonzero constant charge on the increments is a
rational shift coboundary.  The Hölder eliminator that proves this is indifferent to where the
variables come from, so the same argument applies to a whole family of such elements at once: the
variables are the jets of every member, and the charge is a matrix.

For the shifted digammas the charge matrix condition is the orbit-residue statement, and pairwise
incongruent shifts satisfy it.  Hence a finite family of pairwise incongruent shifted digammas is
differentially independent over `ℂ(X)` in the global meromorphic differential field.
-/

open Filter Set Topology Function

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

open MvPolynomial Bottcher

local instance shiftedDigammaDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance shiftedDigammaIntAlgebraAnalytic :
    Algebra ℤ (analyticSubring (Set.univ : Set ℂ)) := Ring.toIntAlgebra _

local instance shiftedDigammaIntAlgebraMero :
    Algebra ℤ (meroField (Set.univ : Set ℂ)) := Ring.toIntAlgebra _

local instance shiftedDigammaIntAlgebraRatFunc :
    Algebra ℤ (RatFunc ℂ) := Ring.toIntAlgebra _

local instance shiftedDigammaDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- **Algebraic independence from rational shift increments.**  A finite family whose members each
translate by a rational increment is algebraically independent over `ℂ(X)` as soon as no nonzero
constant combination of those increments is a rational shift coboundary. -/
theorem algebraicIndependent_of_rationalShiftIncrements
    {L : Type*} [Field L] [Algebra (RatFunc ℂ) L]
    (sigma : L ≃+* L)
    (hbase : ∀ q : RatFunc ℂ,
      sigma (algebraMap (RatFunc ℂ) L q) = algebraMap (RatFunc ℂ) L (ratShift q))
    {m : ℕ} (xj : Fin m → L) (rj : ℕ → RatFunc ℂ)
    (hjet : ∀ j : Fin m, sigma (xj j) = xj j + algebraMap (RatFunc ℂ) L (rj (j : ℕ)))
    (Hres : ∀ {w : RatFunc ℂ} {delta : Fin m → ℂ},
      ratShift w - w = ∑ j : Fin m, algebraMap ℂ (RatFunc ℂ) (delta j) * rj (j : ℕ) →
      ∀ j, delta j = 0) :
    AlgebraicIndependent (RatFunc ℂ) xj := by
  rw [algebraicIndependent_iff_injective_aeval]
  intro P Q hPQ
  have hPQ' : MvPolynomial.eval₂ (algebraMap (RatFunc ℂ) L) xj P =
      MvPolynomial.eval₂ (algebraMap (RatFunc ℂ) L) xj Q := by
    simpa [MvPolynomial.aeval_def] using hPQ
  apply sub_eq_zero.mp
  by_contra hne
  let I : Set (MvPolynomial (Fin m) (RatFunc ℂ)) :=
    {G | MvPolynomial.eval₂ (algebraMap (RatFunc ℂ) L) xj G = 0}
  have hsub : ∀ G H, G ∈ I → H ∈ I → G - H ∈ I := by
    intro G H hG hH
    change MvPolynomial.eval₂ _ _ G = 0 at hG
    change MvPolynomial.eval₂ _ _ H = 0 at hH
    change MvPolynomial.eval₂ _ _ (G - H) = 0
    simp only [MvPolynomial.eval₂_sub, hG, hH, sub_zero]
  have hsmul : ∀ (k : RatFunc ℂ) G, G ∈ I → MvPolynomial.C k * G ∈ I := by
    intro k G hG
    change MvPolynomial.eval₂ _ _ G = 0 at hG
    change MvPolynomial.eval₂ _ _ (MvPolynomial.C k * G) = 0
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hG, mul_zero]
  have hshift : ∀ G, G ∈ I →
      RationalIncrementHolder.jetTranslateWith rj m G ∈ I := by
    intro G hG
    change MvPolynomial.eval₂ _ _
      (RationalIncrementHolder.jetTranslateWith rj m G) = 0
    rw [eval₂_jetTranslateWith sigma hbase rj xj hjet G, hG, map_zero]
  have hconst : ∀ k : RatFunc ℂ, MvPolynomial.C k ∈ I → k = 0 := by
    intro k hk
    change MvPolynomial.eval₂ _ _ (MvPolynomial.C k) = 0 at hk
    simp only [MvPolynomial.eval₂_C] at hk
    exact (algebraMap (RatFunc ℂ) L).injective (hk.trans (map_zero _).symm)
  have hrel : P - Q ∈ I := by
    change MvPolynomial.eval₂ _ _ (P - Q) = 0
    rw [MvPolynomial.eval₂_sub]
    exact sub_eq_zero.mpr hPQ'
  exact RationalIncrementHolder.no_shift_stable_annihilatorWith rj I
    hsub hsmul hshift hconst Hres ⟨P - Q, hrel, hne⟩

/-- **Differential independence from a rational increment matrix.**  A finite family of elements
whose unit-shift increments are rational is differentially independent over `ℂ(X)` as soon as no
nonzero constant charge matrix on the increment jets is a rational shift coboundary. -/
theorem differentialIndependent_of_rationalShiftIncrements
    {L : Type*} [Field L] [Algebra (RatFunc ℂ) L] [Differential L] [Differential (RatFunc ℂ)]
    (sigma : L ≃+* L)
    (hbase : ∀ q : RatFunc ℂ,
      sigma (algebraMap (RatFunc ℂ) L q) = algebraMap (RatFunc ℂ) L (ratShift q))
    (hderiv : ∀ y : L, sigma y′ = (sigma y)′)
    (hmap : ∀ q : RatFunc ℂ,
      (algebraMap (RatFunc ℂ) L q)′ = algebraMap (RatFunc ℂ) L q′)
    {r : ℕ} (x : Fin r → L) (b : Fin r → RatFunc ℂ)
    (hshift : ∀ i, sigma (x i) = x i + algebraMap (RatFunc ℂ) L (b i))
    (Hres : ∀ (N : ℕ) (w : RatFunc ℂ) (delta : Fin r → Fin (N + 1) → ℂ),
      ratShift w - w = ∑ i : Fin r, ∑ j : Fin (N + 1),
          algebraMap ℂ (RatFunc ℂ) (delta i j) * differentialJet (j : ℕ) (b i) →
      ∀ i j, delta i j = 0) :
    DifferentialIndependent (RatFunc ℂ) x := by
  classical
  have hjetMap : ∀ (n : ℕ) (q : RatFunc ℂ),
      differentialJet n (algebraMap (RatFunc ℂ) L q)
        = algebraMap (RatFunc ℂ) L (differentialJet n q) := by
    intro n
    induction n with
    | zero => intro q; simp
    | succ n ih =>
        intro q
        rw [differentialJet_succ, ih, hmap, differentialJet_succ]
  have hjetShift : ∀ (i : Fin r) (n : ℕ),
      sigma (differentialJet n (x i)) = differentialJet n (x i)
        + algebraMap (RatFunc ℂ) L (differentialJet n (b i)) := by
    intro i n
    rw [ringEquiv_differentialJet (fun _ : Unit => sigma) (fun _ y => hderiv y) () n (x i),
      hshift, differentialJet_additive, hjetMap]
  unfold DifferentialIndependent
  apply algebraicIndependent_of_finite_type
  intro t ht
  letI : Fintype t := ht.fintype
  set N : ℕ := ht.toFinset.sup (fun p => p.2) with hN
  have hle : ∀ p ∈ t, p.2 < N + 1 := by
    intro p hp
    have : p.2 ≤ N := by
      rw [hN]
      exact Finset.le_sup (f := fun p : Fin r × ℕ => p.2) (by simpa using hp)
    omega
  set E : Fin r × Fin (N + 1) ≃ Fin (r * (N + 1)) := finProdFinEquiv with hE
  set xj : Fin (r * (N + 1)) → L :=
    fun k => differentialJet ((E.symm k).2 : ℕ) (x (E.symm k).1) with hxj
  set rj : ℕ → RatFunc ℂ := fun n =>
    if h : n < r * (N + 1) then
      differentialJet ((E.symm ⟨n, h⟩).2 : ℕ) (b (E.symm ⟨n, h⟩).1)
    else 0 with hrj
  have hrjk : ∀ k : Fin (r * (N + 1)),
      rj (k : ℕ) = differentialJet ((E.symm k).2 : ℕ) (b (E.symm k).1) := by
    intro k
    rw [hrj]
    simp only [k.isLt, dif_pos, Fin.eta]
  have hjetxj : ∀ k : Fin (r * (N + 1)),
      sigma (xj k) = xj k + algebraMap (RatFunc ℂ) L (rj (k : ℕ)) := by
    intro k
    rw [hxj, hrjk k]
    exact hjetShift (E.symm k).1 ((E.symm k).2 : ℕ)
  have Hres' : ∀ {w : RatFunc ℂ} {delta : Fin (r * (N + 1)) → ℂ},
      ratShift w - w = ∑ k : Fin (r * (N + 1)),
        algebraMap ℂ (RatFunc ℂ) (delta k) * rj (k : ℕ) → ∀ k, delta k = 0 := by
    intro w delta hsum
    have hrewrite : (∑ k : Fin (r * (N + 1)),
          algebraMap ℂ (RatFunc ℂ) (delta k) * rj (k : ℕ))
        = ∑ i : Fin r, ∑ j : Fin (N + 1),
            algebraMap ℂ (RatFunc ℂ) (delta (E (i, j))) * differentialJet (j : ℕ) (b i) := by
      have h1 := Fintype.sum_prod_type'
        (f := fun (i : Fin r) (j : Fin (N + 1)) =>
          algebraMap ℂ (RatFunc ℂ) (delta (E (i, j))) * differentialJet ((j : ℕ)) (b i))
      rw [← h1]
      refine (Fintype.sum_equiv E _ _ fun p => ?_).symm
      rw [hrjk (E p), Equiv.symm_apply_apply]
    rw [hrewrite] at hsum
    have hzero := Hres N w (fun i j => delta (E (i, j))) hsum
    intro k
    have := hzero (E.symm k).1 (E.symm k).2
    rwa [Prod.mk.eta, Equiv.apply_symm_apply] at this
  have hindep : AlgebraicIndependent (RatFunc ℂ) xj :=
    algebraicIndependent_of_rationalShiftIncrements sigma hbase xj rj hjetxj Hres'
  set f : t → Fin (r * (N + 1)) :=
    fun p => E (p.1.1, ⟨p.1.2, hle p.1 p.2⟩) with hf
  have hfinj : Function.Injective f := by
    intro p q hpq
    have h1 : (p.1.1, (⟨p.1.2, hle p.1 p.2⟩ : Fin (N + 1)))
        = (q.1.1, (⟨q.1.2, hle q.1 q.2⟩ : Fin (N + 1))) := E.injective hpq
    have h2 : p.1.1 = q.1.1 :=
      congrArg (fun z : Fin r × Fin (N + 1) => z.1) h1
    have h3 : p.1.2 = q.1.2 :=
      congrArg (fun z : Fin r × Fin (N + 1) => (z.2 : ℕ)) h1
    exact Subtype.ext (Prod.ext h2 h3)
  have hcomp := hindep.comp f hfinj
  have hfun : xj ∘ f = fun p : t => differentialJet p.1.2 (x p.1.1) := by
    funext p
    rw [Function.comp_apply, hxj, hf]
    simp
  rwa [hfun] at hcomp

/-- The rational increment of the jet of order `j` of `ψ(s+λ_i)` is the `j`-th coordinate
derivative of `1/(X+λ_i)`. -/
theorem differentialJet_one_div_shift {r : ℕ} (lam : Fin r → ℂ) (i : Fin r) (j : ℕ) :
    letI := ratFuncCoordinateDifferential
    differentialJet j (1 / (RatFunc.X + RatFunc.C (lam i)))
      = familyIncrement lam i j := by
  letI := ratFuncCoordinateDifferential
  have hbase : (1 : RatFunc ℂ) / (RatFunc.X + RatFunc.C (lam i))
      = gammaOrbitIncrement (fun _ : Fin 1 => lam i) (fun _ => 1) 0 := by
    rw [gammaOrbitIncrement]
    simp
  have hstep : ∀ n : ℕ,
      differentialJet n (gammaOrbitIncrement (fun _ : Fin 1 => lam i) (fun _ => 1) 0)
        = gammaOrbitIncrement (fun _ : Fin 1 => lam i) (fun _ => 1) n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [differentialJet_succ, ih]
        exact ratFuncCoordinateDerivation_gammaOrbitIncrement _ _ n
  rw [hbase, hstep j, familyIncrement, gammaOrbitIncrement]
  simp

/-- **Theorem A.**  Finitely many pairwise incongruent shifted digammas are differentially
independent over `ℂ(X)` in the global meromorphic differential field.  The unit shift moves each
member by a rational increment, and no nonzero constant charge matrix on the increment jets is a
rational shift coboundary. -/
theorem differentialIndependent_digammaShiftMero {r : ℕ} (lam : Fin r → ℂ)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, lam i - lam i' ≠ (n : ℂ)) :
    letI : Algebra (RatFunc ℂ) (meroField Set.univ) :=
      (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ).toAlgebra
    DifferentialIndependent (RatFunc ℂ) (fun i => digammaShiftMero (lam i)) := by
  letI : Algebra (RatFunc ℂ) (meroField Set.univ) :=
    (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ).toAlgebra
  letI := ratFuncCoordinateDifferential
  refine differentialIndependent_of_rationalShiftIncrements
    (addTranslationMeroEquiv 1) (fun q => addTranslationMeroEquiv_ratfuncToMero q)
    (fun y => addTranslationMeroEquiv_deriv 1 y)
    (fun q => meroField_deriv_ratfuncToMero q)
    (fun i => digammaShiftMero (lam i))
    (fun i => 1 / (RatFunc.X + RatFunc.C (lam i)))
    (fun i => addTranslationMeroEquiv_digammaShiftMero (lam i)) ?_
  intro N w delta hsum
  refine ratShift_sub_familyIncrement_combination lam hincong (w := w) (delta := delta) ?_
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [differentialJet_one_div_shift lam i (j : ℕ)]

end

end GaloisForLFunctions.HTGeometry
