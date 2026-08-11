import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.PhaseSubdiscriminantKaehlerSmith
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.UltrametricHorizonEnergySmith
import GaloisForLFunctions.HTGeometry.CommonFactorKoszulHomology

/-!
# Prime-radial excess: orientation, discriminant order, and the observer staircase

Prime holonomy defects `f_p = a·u_p` with unit residues share one simple radial factor.  Their
orientation is `a^{N(N−1)/2}` times a unit, so the discriminant divisor is `N(N−1)` times the
horizon and its normalisation is cutoff-independent; the sheet-evaluation observer has the exact
Smith staircase `diag(1, a, …, a^{N−1})`, whose cokernel is the type `A_{N−1}` height
distribution.
-/

namespace HTGeometry.ConstraintRelativity

open GaloisForLFunctions.HTGeometry IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-! ## The orientation of a common-contact configuration -/

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(20)`.**  The orientation of common-contact sheets is the contact parameter to the
triangular power times the residue orientation. -/
theorem vandermondeProd_contactSheets {N : ℕ} (c : R) (u : Fin N → R) :
    vandermondeProd (contactSheets c u)
      = c ^ (∑ i : Fin N, (i : ℕ)) * vandermondeProd u := by
  classical
  rw [vandermondeProd, vandermondeProd]
  have hfac : ∀ i : Fin N, ∏ j ∈ Finset.Ioi i, (contactSheets c u j - contactSheets c u i)
      = c ^ (Finset.Ioi i).card * ∏ j ∈ Finset.Ioi i, (u j - u i) := by
    intro i
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    show c * u j - c * u i = c * (u j - u i)
    ring
  rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  congr 2
  have hcard : ∀ i : Fin N, (Finset.Ioi i).card = ((i.rev : Fin N) : ℕ) := by
    intro i
    rw [Fin.card_Ioi, Fin.val_rev]
    omega
  rw [Finset.sum_congr rfl fun i _ => hcard i]
  exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin N)) fun i : Fin N => (i : ℕ)

/-- The valuation of a power. -/
theorem addVal_pow (c : R) (n : ℕ) : addVal R (c ^ n) = n • addVal R c := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, (addVal R).map_mul, ih, succ_nsmul]

/-- **Card `(17)`, `(18)`.**  The discriminant of a common-contact configuration has order exactly
`N(N−1)` in the contact parameter. -/
theorem addVal_sheetDiscriminant_contact {N : ℕ} (c : R) (u : Fin N → R)
    (hu : ∀ i j : Fin N, i ≠ j → IsUnit (u j - u i)) :
    addVal R (sheetDiscriminant (contactSheets c u))
      = (2 * ∑ i : Fin N, (i : ℕ)) • addVal R c := by
  have huP : IsUnit (vandermondeProd u) := by
    rw [← det_vandermonde_eq_vandermondeProd]
    exact isUnit_det_vandermonde_of_separated u hu
  rw [sheetDiscriminant, vandermondeProd_contactSheets, mul_pow, ← pow_mul,
    (addVal R).map_mul, addVal_of_isUnit (huP.pow 2), add_zero, addVal_pow, mul_comm]


/-! ## The observer staircase and the square law -/

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(20c)`, `(20d)`, boxed.**  The prime-radial observer has the exact Smith staircase
`diag(1, a, …, a^{N−1})`, so its cokernel is `⊕_j R/(a^j)`. -/
theorem primeRadial_cokernel_equiv {N : ℕ} (c : R) (u : Fin N → R)
    (hu : ∀ i j : Fin N, i ≠ j → IsUnit (u j - u i)) :
    Nonempty (((Fin N → R) ⧸ LinearMap.range (Matrix.vandermonde (contactSheets c u)).mulVecLin)
      ≃ₗ[R] ∀ j : Fin N, R ⧸ (Ideal.span {c ^ (j : ℕ)} : Submodule R R)) :=
  contact_cokernel_equiv c u hu

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(20c)`.**  Every determinantal ideal of the prime-radial observer is the triangular
power of the horizon parameter. -/
theorem primeRadial_detIdeal {N : ℕ} (c : R) (u : Fin N → R)
    (hu : ∀ i j : Fin N, i ≠ j → IsUnit (u j - u i)) {k : ℕ} (hk : k ≤ N) :
    detIdeal (Matrix.vandermonde (contactSheets c u)) k
      = Ideal.span {c ^ (∑ α : Fin k, (α : ℕ))} :=
  detIdeal_contact c u hu hk

omit [IsDiscreteValuationRing R] in
/-- **Card `(20j)`, boxed.**  The observer orientation ideal squares to the cotangent Fitting
ideal, at every height. -/
theorem primeRadial_fitting_square {N : ℕ} (c : R) (u : Fin N → R) (hN : 0 < N)
    (hu : ∀ i j : Fin N, i ≠ j → IsUnit (u j - u i)) {k : ℕ} (hk : k ≤ N)
    (hsw : IsUnit (phaseSubdiscriminant u k)) :
    detIdeal (contactScale c (residueMult u)) k
      = detIdeal (Matrix.vandermonde (contactSheets c u)) k ^ 2 :=
  detIdeal_contactScale_eq_sq c u hN hu hk hsw

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(20f)`.**  The `a`-adic grade dimensions of the observer defect are `N−1, N−2, …, 1`:
in grade `k` exactly the summands of index above `k` survive. -/
theorem primeRadial_grade_card (N k : ℕ) :
    ((Finset.univ : Finset (Fin N)).filter (fun j : Fin N => k < (j : ℕ))).card = N - 1 - k := by
  classical
  rcases Nat.lt_or_ge k N with hk | hk
  · have hset : ((Finset.univ : Finset (Fin N)).filter (fun j : Fin N => k < (j : ℕ)))
        = Finset.Ioi (⟨k, hk⟩ : Fin N) := by
      ext j
      simp [Finset.mem_Ioi, Fin.lt_def]
    rw [hset, Fin.card_Ioi]
  · have hempty : ((Finset.univ : Finset (Fin N)).filter (fun j : Fin N => k < (j : ℕ))) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_lt]
      intro _
      exact le_trans (Nat.le_of_lt_succ (Nat.lt_succ_of_lt j.isLt)) hk
    rw [hempty, Finset.card_empty]
    omega

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(20f)`.**  The grade dimensions match the type `A_{N−1}` positive-root height
distribution: height `h = k + 1` has `N − h` positive roots. -/
theorem primeRadial_grade_eq_rootCount (N k : ℕ) :
    ((Finset.univ : Finset (Fin N)).filter (fun j : Fin N => k < (j : ℕ))).card
      = N - (k + 1) := by
  rw [primeRadial_grade_card]
  omega


/-! ## The weighted root conormal -/

section RootConormal

variable {k : Type*} [Field k] {N : ℕ}

/-- The weighted syzygy functional `c ↦ ∑ c_p w_p`. -/
def weightedSum (w : Fin N → k) : (Fin N → k) →ₗ[k] k where
  toFun c := ∑ i, c i * w i
  map_add' c d := by
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **Card `(12)`.**  The mean-zero type `A_{N−1}` root space. -/
def meanSum : (Fin N → k) →ₗ[k] k := weightedSum (fun _ => 1)

/-- **Card `(11)`.**  The weighted diagonal isomorphism. -/
noncomputable def weightDiag (w : Fin N → k) (hw : ∀ i, w i ≠ 0) :
    (Fin N → k) ≃ₗ[k] (Fin N → k) where
  toFun c := fun i => c i * w i
  map_add' c d := by
    funext i
    show (c i + d i) * w i = c i * w i + d i * w i
    ring
  map_smul' a c := by
    funext i
    show (a * c i) * w i = a * (c i * w i)
    ring
  invFun d := fun i => d i / w i
  left_inv c := by
    funext i
    show c i * w i / w i = c i
    field_simp [hw i]
  right_inv d := by
    funext i
    show d i / w i * w i = d i
    field_simp [hw i]

/-- **Cards `(10)`–`(12)`, boxed.**  The weighted diagonal carries the weighted syzygy hyperplane
isomorphically onto the mean-zero root space. -/
theorem weightDiag_map_ker (w : Fin N → k) (hw : ∀ i, w i ≠ 0) :
    Submodule.map (weightDiag w hw).toLinearMap (LinearMap.ker (weightedSum w))
      = LinearMap.ker (meanSum : (Fin N → k) →ₗ[k] k) := by
  ext d
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : ∑ i, c i * w i = 0 := hc
    show ∑ i, ((weightDiag w hw).toLinearMap c) i * 1 = 0
    rw [← hc']
    exact Finset.sum_congr rfl fun i _ => by
      show c i * w i * 1 = c i * w i
      ring
  · intro hd
    have hd' : ∑ i, d i * 1 = 0 := hd
    refine ⟨fun i => d i / w i, ?_, ?_⟩
    · show ∑ i, (d i / w i) * w i = 0
      rw [← hd']
      exact Finset.sum_congr rfl fun i _ => by
        field_simp [hw i]
    · funext i
      show d i / w i * w i = d i
      field_simp [hw i]

/-- **Card `(13)`.**  The weighted syzygy functional is surjective, so the underived horizon port
is one-dimensional. -/
theorem weightedSum_surjective {w : Fin N → k} {i₀ : Fin N} (hw : w i₀ ≠ 0) :
    Function.Surjective (weightedSum w) := by
  classical
  intro y
  refine ⟨fun i => if i = i₀ then y / w i₀ else 0, ?_⟩
  show ∑ i, (if i = i₀ then y / w i₀ else 0) * w i = y
  rw [Finset.sum_eq_single i₀]
  · rw [if_pos rfl]
    field_simp
  · intro j _ hj
    rw [if_neg hj, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

/-- **Card `(14)`.**  The excess conormal has rank `N − 1`. -/
theorem finrank_ker_weightedSum {w : Fin N → k} {i₀ : Fin N} (hw : w i₀ ≠ 0) :
    Module.finrank k (LinearMap.ker (weightedSum w)) = N - 1 := by
  have hrange : LinearMap.range (weightedSum w) = ⊤ :=
    LinearMap.range_eq_top.mpr (weightedSum_surjective hw)
  have hrk := LinearMap.finrank_range_add_finrank_ker (weightedSum w)
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_pi] at hrk
  simp only [Fintype.card_fin] at hrk
  omega

end RootConormal


/-! ## Koszul homology of the prime holonomy defects -/

section Koszul

set_option maxSynthPendingDepth 4

/-- The `(p+1)`-st Koszul homology in split coordinates. -/
abbrev splitKoszulHomology (z : R) (E : Type*) [AddCommGroup E] [Module R E] (p : ℕ) :=
  ↥(splitCommonFactorKoszulCycles z E p) ⧸ splitCommonFactorKoszulBoundaries z E p

/-- **Card `(5)`, `(9)`, boxed.**  In split coordinates the Koszul homology of a common-factor
family is the exterior power of the excess conormal modulo the common factor:
`H_{p+1}(K) ≅ (⋀^{p+1}E) ⧸ z·(⋀^{p+1}E)`. -/
noncomputable def splitKoszulHomologyEquiv {z : R} (hz : z ≠ 0)
    (E : Type*) [AddCommGroup E] [Module R E] (p : ℕ)
    [NoZeroSMulDivisors R (⋀[R]^p E)] :
    (↥(⋀[R]^(p + 1) E) ⧸ LinearMap.range (commonFactorScalarMap z :
        ↥(⋀[R]^(p + 1) E) →ₗ[R] ↥(⋀[R]^(p + 1) E)))
      ≃ₗ[R] splitKoszulHomology z E p :=
  Submodule.Quotient.equiv _ _ (splitCommonFactorCyclesEquiv hz E p)
    (map_scalarRange_splitCommonFactorCyclesEquiv_eq_boundaries hz E p)

end Koszul


/-- **Card `(6)`, boxed.**  The Koszul homology dimensions are the binomial coefficients of the
excess conormal rank. -/
theorem finrank_exteriorPower_ker_weightedSum {k : Type*} [Field k] {N : ℕ} {w : Fin N → k}
    {i₀ : Fin N} (hw : w i₀ ≠ 0) (j : ℕ) :
    Module.finrank k (⋀[k]^j (LinearMap.ker (weightedSum w))) = (N - 1).choose j := by
  rw [exteriorPower.finrank_eq k j, finrank_ker_weightedSum hw]

/-! ## The canonical root frame -/

section RootFrame

variable {N : ℕ}

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(22f)`.**  The canonical root frame `s_p = u_p⁻¹ e_p` is normalised by the
augmentation. -/
theorem rootFrame_normalised (u : Fin N → Rˣ) (p : Fin N) :
    unitWeightedAugmentation u (unitWeightedSection u p 1) = 1 :=
  unitWeightedAugmentation_section u p 1

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(22g)`.**  Ordered differences of the root frame are excess syzygies. -/
theorem rootDifference_mem_relations (u : Fin N → Rˣ) (p q : Fin N) :
    unitWeightedSection u p 1 - unitWeightedSection u q 1 ∈ unitWeightedRelations u := by
  rw [LinearMap.mem_ker, map_sub, unitWeightedAugmentation_section,
    unitWeightedAugmentation_section, sub_self]

end RootFrame


/-! ## Phase-torus conormal curvature and unbounded degree -/

section PhaseCurvature

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- **Card `(22e)`, boxed.**  The determinant-line curvature is flat: every commutator has zero
trace, so the trace of the phase curvature vanishes. -/
theorem trace_commutator_eq_zero [Module.Finite k V] [Module.Free k V] (P Q : Module.End k V) :
    LinearMap.trace k V (P * Q - Q * P) = 0 := by
  rw [map_sub, LinearMap.trace_mul_comm, sub_self]

/-- **Card `(22d)`, `N = 2`.**  On a one-dimensional excess bundle every pair commutator
vanishes, so the phase curvature is zero. -/
theorem commutator_eq_zero_of_finrank_one (h : Module.finrank k V = 1)
    (P Q : Module.End k V) : P * Q - Q * P = 0 := by
  haveI : Module.Finite k V := Module.finite_of_finrank_pos (by omega)
  have hcomm : ∀ f g : Module.End k V, f * g = g * f := by
    intro f g
    obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.mp h
    refine LinearMap.ext fun x => ?_
    obtain ⟨c, hc⟩ := hv x
    obtain ⟨a, ha⟩ := hv (f v)
    obtain ⟨b, hb⟩ := hv (g v)
    have hgx : g x = (c * b) • v := by
      rw [← hc, map_smul, ← hb, smul_smul]
    have hfx : f x = (c * a) • v := by
      rw [← hc, map_smul, ← ha, smul_smul]
    show f (g x) = g (f x)
    rw [hgx, hfx, map_smul, map_smul, ← ha, ← hb, smul_smul, smul_smul]
    congr 1
    ring
  rw [hcomm, sub_self]

/-- **Card `(21)`, `(22)`.**  Every fixed exterior degree is born at a finite cutoff, and there is
no largest nonzero degree: the excess conormal of `j + 1` primes already has nonvanishing `j`-th
exterior power. -/
theorem exists_cutoff_exteriorPower_ne_zero (j : ℕ) :
    ∃ N : ℕ, 0 < (N - 1).choose j := by
  refine ⟨j + 1, ?_⟩
  simp

end PhaseCurvature


/-! ## Rank-one phase curvature at three or more primes -/

section RankOne

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The rank-one Hermitian operator `|x⟩⟨x|`. -/
noncomputable def rankOneOp (x : V) : V →ₗ[ℂ] V where
  toFun v := (inner ℂ x v : ℂ) • x
  map_add' u v := by
    show (inner ℂ x (u + v) : ℂ) • x = (inner ℂ x u : ℂ) • x + (inner ℂ x v : ℂ) • x
    rw [inner_add_right, add_smul]
  map_smul' c v := by
    show (inner ℂ x (c • v) : ℂ) • x = c • ((inner ℂ x v : ℂ) • x)
    rw [inner_smul_right, smul_smul]

/-- **Card `(22d)`, `N ≥ 3`.**  Non-orthogonal, non-collinear rank-one Hermitian operators do not
commute, so the phase curvature is nonzero once three primes are present. -/
theorem rankOneOp_not_commute {x y : V} (hxy : (inner ℂ x y : ℂ) ≠ 0) (hy : y ≠ 0)
    (hnc : ∀ c : ℂ, x ≠ c • y) :
    rankOneOp x * rankOneOp y ≠ rankOneOp y * rankOneOp x := by
  intro h
  have hval := congrArg (fun f : V →ₗ[ℂ] V => f y) h
  have hL : (rankOneOp x * rankOneOp y) y
      = ((inner ℂ y y : ℂ) * (inner ℂ x y : ℂ)) • x := by
    show (inner ℂ x ((inner ℂ y y : ℂ) • y) : ℂ) • x = _
    rw [inner_smul_right]
  have hR : (rankOneOp y * rankOneOp x) y
      = ((inner ℂ x y : ℂ) * (inner ℂ y x : ℂ)) • y := by
    show (inner ℂ y ((inner ℂ x y : ℂ) • x) : ℂ) • y = _
    rw [inner_smul_right]
  rw [hL, hR] at hval
  have hyy : (inner ℂ y y : ℂ) ≠ 0 := inner_self_ne_zero.mpr hy
  refine hnc ((inner ℂ y x : ℂ) / (inner ℂ y y : ℂ)) ?_
  have hcancel : (inner ℂ y y : ℂ) • x = (inner ℂ y x : ℂ) • y := by
    refine smul_right_injective V hxy ?_
    show (inner ℂ x y : ℂ) • ((inner ℂ y y : ℂ) • x)
      = (inner ℂ x y : ℂ) • ((inner ℂ y x : ℂ) • y)
    rw [smul_smul, smul_smul, mul_comm (inner ℂ x y : ℂ) (inner ℂ y y : ℂ)]
    exact hval
  rw [div_eq_inv_mul, ← smul_smul, ← hcancel, smul_smul, inv_mul_cancel₀ hyy, one_smul]


/-- The orthogonal projection off a unit vector. -/
noncomputable def orthoProj (w v : V) : V := v - (inner ℂ w v : ℂ) • w

/-- **Card `(22c)`.**  Orthogonal unit vectors project to non-orthogonal ones. -/
theorem inner_orthoProj_orthoProj (w a b : V) (hw : (inner ℂ w w : ℂ) = 1)
    (hab : (inner ℂ a b : ℂ) = 0) :
    (inner ℂ (orthoProj w a) (orthoProj w b) : ℂ)
      = -((inner ℂ a w : ℂ) * (inner ℂ w b : ℂ)) := by
  rw [orthoProj, orthoProj, inner_sub_left, inner_sub_right, inner_sub_right,
    inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right, hab, hw,
    inner_conj_symm]
  ring

/-- **Card `(22d)`, `N ≥ 3`.**  A third direction meeting the weight vector separates the two
projected basis vectors, so they are not collinear. -/
theorem orthoProj_not_collinear {w a b c : V} (haa : (inner ℂ a a : ℂ) = 1)
    (hab : (inner ℂ a b : ℂ) = 0) (hca : (inner ℂ c a : ℂ) = 0) (hcb : (inner ℂ c b : ℂ) = 0)
    (hcw : (inner ℂ c w : ℂ) ≠ 0) (l : ℂ) :
    orthoProj w a ≠ l • orthoProj w b := by
  intro hcol
  have hpair : ∀ v : V, (inner ℂ v (orthoProj w a) : ℂ)
      = l * (inner ℂ v (orthoProj w b) : ℂ) := by
    intro v
    rw [hcol, inner_smul_right]
  have hc := hpair c
  rw [orthoProj, orthoProj, inner_sub_right, inner_sub_right, hca, hcb, inner_smul_right,
    inner_smul_right, zero_sub, zero_sub] at hc
  have hwab : (inner ℂ w a : ℂ) = l * (inner ℂ w b : ℂ) := by
    refine mul_right_cancel₀ hcw ?_
    linear_combination -hc
  have ha := hpair a
  rw [orthoProj, orthoProj, inner_sub_right, inner_sub_right, haa, hab, inner_smul_right,
    inner_smul_right, zero_sub] at ha
  have hone : (1 : ℂ) = 0 := by
    rw [hwab] at ha
    linear_combination ha
  exact one_ne_zero hone


/-- **Card `(22d)`, boxed.**  With three or more primes every pair commutator of the phase
curvature is nonzero: the excess bundle carries traceless non-Abelian phase curvature. -/
theorem phaseCurvature_commutator_ne_zero {w a b c : V} (hw : (inner ℂ w w : ℂ) = 1)
    (haa : (inner ℂ a a : ℂ) = 1) (hab : (inner ℂ a b : ℂ) = 0)
    (hca : (inner ℂ c a : ℂ) = 0) (hcb : (inner ℂ c b : ℂ) = 0)
    (hcw : (inner ℂ c w : ℂ) ≠ 0) (haw : (inner ℂ a w : ℂ) ≠ 0)
    (hwb : (inner ℂ w b : ℂ) ≠ 0) :
    rankOneOp (orthoProj w a) * rankOneOp (orthoProj w b)
      ≠ rankOneOp (orthoProj w b) * rankOneOp (orthoProj w a) := by
  have hinner : (inner ℂ (orthoProj w a) (orthoProj w b) : ℂ) ≠ 0 := by
    rw [inner_orthoProj_orthoProj w a b hw hab]
    exact neg_ne_zero.mpr (mul_ne_zero haw hwb)
  have hbne : orthoProj w b ≠ 0 := by
    intro h0
    rw [h0, inner_zero_right] at hinner
    exact hinner rfl
  exact rankOneOp_not_commute hinner hbne (orthoProj_not_collinear haa hab hca hcb hcw)

end RankOne






/-! ## Compatible infinite excess -/

section InfiniteExcess

variable {ι κ : Type*}

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(21)`.**  Zero extension along an injection of prime sets carries excess conormals into
excess conormals: the finite relation modules form a compatible system. -/
theorem mapDomain_mem_unitWeightedFinsuppRelations [DecidableEq κ] (u : κ → Rˣ) (f : ι → κ)
    (hf : Function.Injective f) {x : ι →₀ R}
    (hx : x ∈ unitWeightedFinsuppRelations (u ∘ f)) :
    Finsupp.mapDomain f x ∈ unitWeightedFinsuppRelations u := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [unitWeightedFinsuppAugmentation, Finsupp.lsum_apply,
    Finsupp.sum_mapDomain_index_inj hf]
  rw [unitWeightedFinsuppAugmentation, Finsupp.lsum_apply] at hx
  exact hx

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(21)`, `(22)`, boxed.**  Over an infinite prime set the excess conormal has an infinite
free basis, so no exterior degree is the top one: there is no stable top determinant. -/
theorem infinite_unitWeightedFinsuppAway [Infinite ι] (i₀ : ι) :
    Infinite (unitWeightedFinsuppAway i₀) := by
  have hcompl : {i : ι | i ≠ i₀}.Infinite := by
    have hset : {i : ι | i ≠ i₀} = ({i₀} : Set ι)ᶜ := by
      ext i
      simp
    rw [hset]
    exact Set.Finite.infinite_compl (Set.finite_singleton i₀)
  exact Set.infinite_coe_iff.mpr hcompl

end InfiniteExcess

end HTGeometry.ConstraintRelativity
