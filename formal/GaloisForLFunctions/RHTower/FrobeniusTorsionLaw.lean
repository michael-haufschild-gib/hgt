import Mathlib
import GaloisForLFunctions.RHTower.XiArakelovKroneckerChamber
import GaloisForLFunctions.RHTower.XiArakelovHurwitzAlgebraicityCollision
import GaloisForLFunctions.RHTower.GlobalParityWall

/-!
# The Frobenius torsion law: integral Arakelov coordinates of the zeros are torsion

In the Arakelov coordinate `w(ρ) = 1 − 1/ρ` the critical line is the unit circle.  A Frobenius
of Weil–Deligne type acting on the divisor of ξ would make every `w(ρ)` an algebraic integer whose
Galois conjugates are again coordinates of zeros (*faithfulness*).  Under RH all coordinates lie on
the unit circle, so by Kronecker's theorem every `w(ρ)` is a root of unity.  The Galois orbit of a
primitive `m`-th root of unity contains `exp(2πi k/m)` with `m ≤ 4k ≤ 3m`, whose preimage
`1/(1 − z)` lies in the closed unit disc.  Infinitely many zeros force infinitely many orders `m`,
hence infinitely many zeros in the closed unit disc, which accumulate; ξ would vanish
identically.

Consequences.
* Integrality together with faithfulness refutes RH; together with the contractive-packet
  orientation of `XiArakelovKroneckerChamber` (which implies RH) it is contradictory.  The
  Weil–Deligne template cannot be transported to ξ in the normalised coordinate: over `𝔽_q` the
  eigenvalues have modulus `q^{1/2} ≠ 1` and escape Kronecker; over ξ the scale is `1`.
* Per-prime integrality `p^ρ` algebraic and normalised integrality `w(ρ)` algebraic exclude each
  other at every nonreal `ρ` (Gelfond–Schneider).
-/

open Complex Polynomial Filter Topology
open scoped Real IntermediateField

namespace RHTower

open GaloisForLFunctions (arakelovW)

/-! ### Kronecker: an algebraic integer with unit-norm conjugates is a root of unity -/

/-- An algebraic integer all of whose Galois conjugates have norm one is a root of unity. -/
theorem exists_pow_eq_one_of_isIntegral_of_conjugates_norm_one {w : ℂ}
    (hw : IsIntegral ℤ w) (hconj : ∀ z ∈ (minpoly ℚ w).rootSet ℂ, ‖z‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ w ^ n = 1 := by
  have hwQ : IsIntegral ℚ w := hw.tower_top
  haveI : FiniteDimensional ℚ ℚ⟮w⟯ := IntermediateField.adjoin.finiteDimensional hwQ
  haveI : NumberField ℚ⟮w⟯ := NumberField.mk
  set x : ℚ⟮w⟯ := IntermediateField.AdjoinSimple.gen ℚ w with hxdef
  have hxw : algebraMap ℚ⟮w⟯ ℂ x = w := IntermediateField.AdjoinSimple.algebraMap_gen ℚ w
  have hinj : Function.Injective (algebraMap ℚ⟮w⟯ ℂ) := (algebraMap ℚ⟮w⟯ ℂ).injective
  have hxint : IsIntegral ℤ x := by
    rw [← isIntegral_algebraMap_iff hinj, hxw]
    exact hw
  have hnorm : ∀ φ : ℚ⟮w⟯ →+* ℂ, ‖φ x‖ = 1 := by
    intro φ
    apply hconj
    have hmem : φ x ∈ Set.range (fun ψ : ℚ⟮w⟯ →+* ℂ => ψ x) := ⟨φ, rfl⟩
    rw [NumberField.Embeddings.range_eval_eq_rootSet_minpoly ℚ⟮w⟯ ℂ x,
      ← minpoly.algebraMap_eq hinj x, hxw] at hmem
    exact hmem
  obtain ⟨n, hn, hxn⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_eq_one ℚ⟮w⟯ ℂ hxint hnorm
  refine ⟨n, hn, ?_⟩
  have h := congrArg (algebraMap ℚ⟮w⟯ ℂ) hxn
  rwa [map_pow, hxw, map_one] at h

/-! ### A totative in the middle third of every period `m ≥ 8` -/

/-- Every `m ≥ 8` has a totative `k` with `m ≤ 4k ≤ 3m`. -/
theorem exists_middle_totative {m : ℕ} (hm : 8 ≤ m) :
    ∃ k : ℕ, Nat.Coprime k m ∧ m ≤ 4 * k ∧ 4 * k ≤ 3 * m ∧ k < m := by
  rcases Nat.even_or_odd m with ⟨n, hn⟩ | ⟨n, hn⟩
  · rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨n - 1, ?_, by omega, by omega, by omega⟩
      apply Nat.coprime_of_dvd
      intro p hp hpk hpm
      have h2 : p ∣ 2 := by
        have h := Nat.dvd_sub hpm (Dvd.dvd.mul_left hpk 2)
        have hm2 : m - 2 * (n - 1) = 2 := by omega
        rwa [hm2] at h
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
      subst hp2
      omega
    · refine ⟨n - 2, ?_, by omega, by omega, by omega⟩
      apply Nat.coprime_of_dvd
      intro p hp hpk hpm
      have h4 : p ∣ 2 * 2 := by
        have h := Nat.dvd_sub hpm (Dvd.dvd.mul_left hpk 2)
        have hm4 : m - 2 * (n - 2) = 2 * 2 := by omega
        rwa [hm4] at h
      have h2 : p ∣ 2 := by
        rcases (Nat.Prime.dvd_mul hp).mp h4 with h | h <;> exact h
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
      subst hp2
      omega
  · refine ⟨n, ?_, by omega, by omega, by omega⟩
    apply Nat.coprime_of_dvd
    intro p hp hpk hpm
    have h1 : p ∣ 1 := by
      have h := Nat.dvd_sub hpm (Dvd.dvd.mul_left hpk 2)
      have hm1 : m - 2 * n = 1 := by omega
      rwa [hm1] at h
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

/-- The root of unity `exp(2πi k/m)` with `m ≤ 4k ≤ 3m` is at distance at least one from `1`. -/
theorem one_le_norm_one_sub_exp {m k : ℕ} (hm : 0 < m) (h1 : m ≤ 4 * k) (h2 : 4 * k ≤ 3 * m) :
    1 ≤ ‖(1 : ℂ) - Complex.exp (2 * π * I * (k / m))‖ := by
  set θ : ℝ := 2 * π * k / m with hθ
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hexp : Complex.exp (2 * π * I * (k / m)) = Complex.exp ((θ : ℂ) * I) := by
    congr 1
    rw [hθ]
    push_cast
    ring
  have hcos : Real.cos θ ≤ 0 := by
    apply Real.cos_nonpos_of_pi_div_two_le_of_le
    · rw [hθ, le_div_iff₀ hmpos]
      have : (m : ℝ) ≤ 4 * k := by exact_mod_cast h1
      nlinarith [Real.pi_pos]
    · rw [hθ, div_le_iff₀ hmpos]
      have : (4 * k : ℝ) ≤ 3 * m := by exact_mod_cast h2
      nlinarith [Real.pi_pos]
  rw [hexp]
  have hsq : ‖(1 : ℂ) - Complex.exp ((θ : ℂ) * I)‖ ^ 2
      = (1 - Real.cos θ) ^ 2 + Real.sin θ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have h2le : 2 ≤ ‖(1 : ℂ) - Complex.exp ((θ : ℂ) * I)‖ ^ 2 := by
    rw [hsq]
    nlinarith
  nlinarith [norm_nonneg ((1 : ℂ) - Complex.exp ((θ : ℂ) * I))]

/-- Every root of unity of the same order is a Galois conjugate of a primitive root. -/
theorem exp_mem_rootSet_minpoly {w : ℂ} {m : ℕ} (hm : 0 < m) (hw : IsPrimitiveRoot w m)
    {k : ℕ} (hk : Nat.Coprime k m) (hkm : k < m) :
    Complex.exp (2 * π * I * (k / m)) ∈ (minpoly ℚ w).rootSet ℂ := by
  have hz : IsPrimitiveRoot (Complex.exp (2 * π * I * (k / m))) m :=
    (Complex.isPrimitiveRoot_iff _ m hm.ne').mpr ⟨k, hkm, hk, rfl⟩
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hw hm,
    Polynomial.mem_rootSet_of_ne (cyclotomic_ne_zero m ℚ), Polynomial.aeval_def,
    Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hz.isRoot_cyclotomic hm

/-- The preimage of a point at distance at least one from `1` lies in the closed unit disc. -/
theorem norm_le_one_of_arakelovW_eq {ρ z : ℂ} (h : arakelovW ρ = z) (hz : 1 ≤ ‖1 - z‖) :
    ‖ρ‖ ≤ 1 := by
  have hρ : ρ⁻¹ = 1 - z := by
    unfold GaloisForLFunctions.arakelovW at h
    linear_combination -h
  have hnorm : ‖ρ‖⁻¹ = ‖1 - z‖ := by rw [← norm_inv, hρ]
  by_cases h0 : ρ = 0
  · simp [h0]
  · have hpos : 0 < ‖ρ‖ := norm_pos_iff.mpr h0
    rw [← hnorm] at hz
    exact (one_le_inv₀ hpos).mp hz

/-- ξ has infinitely many zeros. -/
theorem xiZeros_infinite : {ρ : ℂ | xi ρ = 0}.Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image Complex.im).bddAbove
  obtain ⟨τ, hτ, hzero, _⟩ := exists_odd_order_line_zero_gt B
  have hmem : (linePt τ).im ∈ Complex.im '' {ρ : ℂ | xi ρ = 0} := ⟨linePt τ, hzero, rfl⟩
  have h := hB hmem
  have him : (linePt τ).im = τ := by simp [linePt]
  rw [him] at h
  linarith

/-! ### The torsion law -/

/-- Faithfulness: every Galois conjugate of the Arakelov coordinate of a zero of ξ is the
Arakelov coordinate of a zero of ξ. -/
def XiArakelovFaithful : Prop :=
  ∀ ρ : ℂ, xi ρ = 0 → ∀ z ∈ (minpoly ℚ (arakelovW ρ)).rootSet ℂ,
    ∃ ρ' : ℂ, xi ρ' = 0 ∧ arakelovW ρ' = z

/-- Unitarity: every zero coordinate lies on the unit circle. -/
def XiArakelovUnitary : Prop := ∀ ρ : ℂ, xi ρ = 0 → ‖arakelovW ρ‖ = 1

/-- Under RH every zero of ξ has real part one half. -/
theorem xi_zero_re_eq_half_of_riemannHypothesis (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : xi ρ = 0) : ρ.re = 1 / 2 := by
  have h := rh_iff_xi_ne_zero_right.mp hRH
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : xi (1 - ρ) = 0 := by rw [xi_one_sub]; exact hρ
    have hmem : (1 - ρ) ∈ rightHalf := by
      rw [mem_rightHalf, Complex.sub_re, Complex.one_re]
      linarith
    exact h _ hmem h1
  · exact h ρ (mem_rightHalf.mpr hgt) hρ

/-- RH is unitarity of the Arakelov coordinates. -/
theorem xiArakelovUnitary_of_riemannHypothesis (hRH : RiemannHypothesis) : XiArakelovUnitary := by
  intro ρ hρ
  have h0 : ρ ≠ 0 := by
    intro h
    subst h
    have := (xi_zero_re_mem_open_unit hρ).1
    simp at this
  exact (GaloisForLFunctions.arakelovW_norm_one_iff_critical ρ h0).mpr
    (xi_zero_re_eq_half_of_riemannHypothesis hRH hρ)

/-- **The Frobenius torsion law.**  Integral, faithful, unitary Arakelov coordinates cannot
exist: Kronecker makes every coordinate a root of unity, the middle totative of each order puts a
conjugate zero in the closed unit disc, and infinitely many orders make those zeros accumulate. -/
theorem not_xiArakelovIntegral_faithful_unitary (hint : XiArakelovCoordinatesIntegral)
    (hfaith : XiArakelovFaithful) (hunit : XiArakelovUnitary) : False := by
  classical
  have hfin : ∀ ρ, xi ρ = 0 → IsOfFinOrder (arakelovW ρ) := by
    intro ρ hρ
    rw [isOfFinOrder_iff_pow_eq_one]
    refine exists_pow_eq_one_of_isIntegral_of_conjugates_norm_one (hint ρ hρ) ?_
    intro z hz
    obtain ⟨ρ', hρ', hz'⟩ := hfaith ρ hρ z hz
    rw [← hz']
    exact hunit ρ' hρ'
  set Z : Set ℂ := {ρ | xi ρ = 0} with hZ
  set ord : ℂ → ℕ := fun ρ => orderOf (arakelovW ρ) with hord
  have hfiber : ∀ m ∈ ord '' Z, {ρ ∈ Z | ord ρ = m}.Finite := by
    intro m hm
    obtain ⟨ρ₀, hρ₀, rfl⟩ := hm
    have hmpos : 0 < ord ρ₀ := orderOf_pos_iff.mpr (hfin ρ₀ hρ₀)
    have hsub : {ρ ∈ Z | ord ρ = ord ρ₀} ⊆
        arakelovW ⁻¹' ((Polynomial.nthRootsFinset (ord ρ₀) (1 : ℂ) : Finset ℂ) : Set ℂ) := by
      intro ρ hρ
      obtain ⟨_, hρm⟩ := hρ
      show arakelovW ρ ∈ ((Polynomial.nthRootsFinset (ord ρ₀) (1 : ℂ) : Finset ℂ) : Set ℂ)
      rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hmpos, ← hρm]
      exact pow_orderOf_eq_one (arakelovW ρ)
    refine Set.Finite.subset ?_ hsub
    exact Set.Finite.preimage
      (Set.injOn_of_injective (fun a b h => GaloisForLFunctions.arakelovW_injective h))
      (Finset.finite_toSet _)
  have himg : (ord '' Z).Infinite := by
    intro hfinimg
    apply xiZeros_infinite
    refine Set.Finite.subset (hfinimg.biUnion hfiber) ?_
    intro ρ hρ
    simp only [Set.mem_iUnion]
    exact ⟨ord ρ, ⟨ρ, hρ, rfl⟩, hρ, rfl⟩
  have hbig : ((ord '' Z) \ Set.Iio 8).Infinite := himg.sdiff (Set.finite_Iio 8)
  have hchoose : ∀ m ∈ (ord '' Z) \ Set.Iio 8,
      ∃ ρ' : ℂ, xi ρ' = 0 ∧ ‖ρ'‖ ≤ 1 ∧ ord ρ' = m := by
    intro m hm
    obtain ⟨⟨ρ, hρ, hρm⟩, hm8⟩ := hm
    have hm : 8 ≤ m := by
      simp only [Set.mem_Iio, not_lt] at hm8
      exact hm8
    have hmpos : 0 < m := by omega
    have hprim : IsPrimitiveRoot (arakelovW ρ) m := by
      rw [← hρm]
      exact IsPrimitiveRoot.orderOf _
    obtain ⟨k, hk, h1, h2, hkm⟩ := exists_middle_totative hm
    have hz : Complex.exp (2 * π * I * (k / m)) ∈ (minpoly ℚ (arakelovW ρ)).rootSet ℂ :=
      exp_mem_rootSet_minpoly hmpos hprim hk hkm
    obtain ⟨ρ', hρ', hw'⟩ := hfaith ρ hρ _ hz
    refine ⟨ρ', hρ', norm_le_one_of_arakelovW_eq hw' (one_le_norm_one_sub_exp hmpos h1 h2), ?_⟩
    show orderOf (arakelovW ρ') = m
    rw [hw']
    exact ((Complex.isPrimitiveRoot_iff _ m hmpos.ne').mpr ⟨k, hkm, hk, rfl⟩).eq_orderOf.symm
  set S : Set ℂ := {ρ' | xi ρ' = 0 ∧ ‖ρ'‖ ≤ 1} with hS
  have hSinf : S.Infinite := by
    apply Set.Infinite.of_image ord
    refine hbig.mono ?_
    intro m hm
    obtain ⟨ρ', hρ', hle, hordm⟩ := hchoose m hm
    exact ⟨ρ', ⟨hρ', hle⟩, hordm⟩
  obtain ⟨x, _, hacc⟩ := hSinf.exists_accPt_of_subset_isCompact
    (isCompact_closedBall (0 : ℂ) 1)
    (fun ρ' hρ' => by simpa [Metric.mem_closedBall] using hρ'.2)
  rw [accPt_iff_frequently] at hacc
  have hfreq : ∃ᶠ z in nhdsWithin x {x}ᶜ, xi z = 0 := by
    rw [frequently_nhdsWithin_iff]
    exact hacc.mono fun y hy => ⟨hy.2.1, Set.mem_compl_singleton_iff.mpr hy.1⟩
  have hxi : AnalyticOnNhd ℂ xi Set.univ :=
    xi_differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hzero := hxi.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ x) hfreq
  exact xi_ne_zero_of_one_le_re (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re) (hzero (Set.mem_univ 2))

/-- Integral faithful Arakelov coordinates refute RH. -/
theorem not_riemannHypothesis_of_xiArakelovIntegral_faithful (hint : XiArakelovCoordinatesIntegral)
    (hfaith : XiArakelovFaithful) : ¬ RiemannHypothesis :=
  fun hRH => not_xiArakelovIntegral_faithful_unitary hint hfaith
    (xiArakelovUnitary_of_riemannHypothesis hRH)

/-- Integrality, contractive conjugate packets, and faithfulness are jointly contradictory: the
first two imply RH, and RH with the first and third is impossible. -/
theorem not_xiArakelovIntegral_contractive_faithful (hint : XiArakelovCoordinatesIntegral)
    (hcontract : XiArakelovConjugateRootsContractive) (hfaith : XiArakelovFaithful) : False :=
  not_riemannHypothesis_of_xiArakelovIntegral_faithful hint hfaith
    (riemannHypothesis_of_xiArakelovCoordinatesIntegral_of_conjugateRootsContractive
      hint hcontract)

/-! ### Per-prime integrality excludes normalised integrality -/

/-- If `p^ρ` is algebraic for one integer `p ≥ 2` and `ρ` is nonreal, then `ρ` is transcendental
(Gelfond–Schneider). -/
theorem not_isAlgebraic_of_nat_cpow_isAlgebraic {ρ : ℂ} (hρ : ρ.im ≠ 0) {p : ℕ} (hp : 2 ≤ p)
    (halg : IsAlgebraic ℚ ((p : ℂ) ^ ρ)) : ¬ IsAlgebraic ℚ ρ := by
  intro hρalg
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp1 : (p : ℂ) ≠ 1 := by exact_mod_cast (by omega : p ≠ 1)
  have hnotrat : ¬ ∃ r : ℚ, ρ = (r : ℂ) := by
    rintro ⟨r, hr⟩
    apply hρ
    rw [hr]
    exact Complex.ratCast_im r
  have hGS := GaloisForLFunctions.RHTower.gelfondSchneider_holds (p : ℂ) ρ
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr (isAlgebraic_nat p)) hp0 hp1
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hρalg) hnotrat
  exact hGS halg

/-- Per-prime integrality of a Frobenius eigenvalue `p^ρ` excludes algebraicity of the Arakelov
coordinate `w(ρ)` at every nonreal `ρ`. -/
theorem not_isAlgebraic_arakelovW_of_nat_cpow_isAlgebraic {ρ : ℂ} (hρ : ρ.im ≠ 0) {p : ℕ}
    (hp : 2 ≤ p) (halg : IsAlgebraic ℚ ((p : ℂ) ^ ρ)) : ¬ IsAlgebraic ℚ (arakelovW ρ) :=
  fun h => not_isAlgebraic_of_nat_cpow_isAlgebraic hρ hp halg (isAlgebraic_rho_of_arakelovW h)

end RHTower
