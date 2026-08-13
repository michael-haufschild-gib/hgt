import GaloisForLFunctions.RHTower.XiHorizontalCollisionChargeEndpoint
import GaloisForLFunctions.RHTower.GaussHodgePencilSourcing
import GaloisForLFunctions.RHTower.PrimeLogIncommensuratePhaseClock

/-!
# Coefficient-faithful two-prime Cesàro carrier for horizontal Xi charge

This module constructs a literal source carrier for the horizontal collision charge. For each
strip-window zero `rho`, prime labels `2` and `3`, and valuation depths `a,b`, its summand is

`m_rho * [chi_2(rho) chi_2(1-conj rho)]^a * [chi_3(rho) chi_3(1-conj rho)]^b`.

Thus local divisor multiplicity, both critical-line reflection orientations, prime labels, and
integer prime-power depths remain visible before scalarization. The reflected character products
are unit phases at times `2 rho.im`. A single prime clock aliases ordinates, but the fixed pair
`(log 2, log 3)` is globally injective. Two-dimensional Cesàro mean square therefore groups
exactly by horizontal ordinate and returns `sum_gamma H_gamma^2`.

After subtracting the local square census, the source excess converges exactly to
`xiHorizontalCollisionCharge T`. Consequently RH is equivalent to vanishing of every source
excess limit, and any eventual absolute bound by a constant strictly below the indivisible
two-unit collision quantum proves RH. A normalized `o(N(T))` estimate does not provide this.

All results are unconditional. The remaining analytic producer is now an explicit source estimate
on this fixed-prime carrier rather than an abstract equality of zero-side transports.
-/

open Complex Set Metric Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def finiteTwoPhasePencil {ι : Type*} (s : Finset ι)
    (c z w : ι → ℂ) (n m : ℕ) : ℂ :=
  ∑ i ∈ s, c i * z i ^ n * w i ^ m

theorem tendsto_finiteTwoPhasePencil_cesaro_star_mul
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c z w : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1) (hw : ∀ i ∈ s, ‖w i‖ = 1)
    (hinj : Set.InjOn (fun i => (z i, w i)) (s : Set ι)) :
    Tendsto
      (fun N : ℕ => ((↑((N : ℝ)⁻¹) : ℂ) ^ 2) *
        ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          star (finiteTwoPhasePencil s c z w n m) *
            finiteTwoPhasePencil s c z w n m)
      atTop (nhds (∑ i ∈ s, star (c i) * c i)) := by
  let pairs : Finset (ι × ι) := s.product s
  let C : ι × ι → ℂ := fun p => star (c p.1) * c p.2
  let Z : ι × ι → ℂ := fun p => star (z p.1) * z p.2
  let W : ι × ι → ℂ := fun p => star (w p.1) * w p.2
  have hZ (p : ι × ι) (hp : p ∈ pairs) : ‖Z p‖ = 1 := by
    have hp' : p.1 ∈ s ∧ p.2 ∈ s := Finset.mem_product.mp (by simpa [pairs] using hp)
    simp [Z, hz p.1 hp'.1, hz p.2 hp'.2]
  have hW (p : ι × ι) (hp : p ∈ pairs) : ‖W p‖ = 1 := by
    have hp' : p.1 ∈ s ∧ p.2 ∈ s := Finset.mem_product.mp (by simpa [pairs] using hp)
    simp [W, hw p.1 hp'.1, hw p.2 hp'.2]
  have hphase (i j : ι) (hi : i ∈ s) (hj : j ∈ s) :
      (Z (i,j) = 1 ∧ W (i,j) = 1) ↔ i = j := by
    rw [show Z (i,j) = 1 ↔ z i = z j from star_mul_eq_one_iff_eq (hz i hi) (hz j hj),
      show W (i,j) = 1 ↔ w i = w j from star_mul_eq_one_iff_eq (hw i hi) (hw j hj)]
    constructor
    · intro h
      exact hinj hi hj (Prod.ext h.1 h.2)
    · rintro rfl
      exact ⟨rfl, rfl⟩
  have hpoint (p : ι × ι) (hp : p ∈ pairs) :
      Tendsto (fun N : ℕ => C p *
          ((↑((N : ℝ)⁻¹) : ℂ) * ∑ n ∈ Finset.range N, Z p ^ n) *
          ((↑((N : ℝ)⁻¹) : ℂ) * ∑ m ∈ Finset.range N, W p ^ m))
        atTop
        (nhds (if Z p = 1 ∧ W p = 1 then C p else 0)) := by
    have hzlim := tendsto_complex_geom_cesaro_of_norm_eq_one (Z p) (hZ p hp)
    have hwlim := tendsto_complex_geom_cesaro_of_norm_eq_one (W p) (hW p hp)
    have hzlim' : Tendsto (fun N : ℕ =>
        ((↑((N : ℝ)⁻¹) : ℂ) * ∑ n ∈ Finset.range N, Z p ^ n))
        atTop (nhds (if Z p = 1 then 1 else 0)) := by
      simpa only [Complex.ofReal_inv] using hzlim
    have hwlim' : Tendsto (fun N : ℕ =>
        ((↑((N : ℝ)⁻¹) : ℂ) * ∑ m ∈ Finset.range N, W p ^ m))
        atTop (nhds (if W p = 1 then 1 else 0)) := by
      simpa only [Complex.ofReal_inv] using hwlim
    have hlim₁ : Tendsto (fun N : ℕ => C p *
        ((↑((N : ℝ)⁻¹) : ℂ) * ∑ n ∈ Finset.range N, Z p ^ n))
        atTop (nhds (C p * (if Z p = 1 then 1 else 0))) :=
      tendsto_const_nhds.mul hzlim'
    have hlim := hlim₁.mul hwlim'
    convert hlim using 1
    split_ifs <;> simp_all
  have hsum := tendsto_finsetSum pairs hpoint
  have hexpand (n m : ℕ) :
      star (finiteTwoPhasePencil s c z w n m) *
          finiteTwoPhasePencil s c z w n m =
        ∑ i ∈ s, ∑ j ∈ s, C (i,j) * Z (i,j) ^ n * W (i,j) ^ m := by
    simp only [finiteTwoPhasePencil, C, Z, W]
    rw [star_sum, Finset.sum_mul]
    simp_rw [star_mul, star_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hreorder (N : ℕ) :
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          ∑ i ∈ s, ∑ j ∈ s, C (i,j) * Z (i,j) ^ n * W (i,j) ^ m =
        ∑ i ∈ s, ∑ j ∈ s, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          C (i,j) * Z (i,j) ^ n * W (i,j) ^ m := by
    calc
      _ = ∑ n ∈ Finset.range N, ∑ i ∈ s, ∑ m ∈ Finset.range N,
            ∑ j ∈ s, C (i,j) * Z (i,j) ^ n * W (i,j) ^ m := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.sum_comm]
      _ = ∑ i ∈ s, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
            ∑ j ∈ s, C (i,j) * Z (i,j) ^ n * W (i,j) ^ m := by
          rw [Finset.sum_comm]
      _ = ∑ i ∈ s, ∑ n ∈ Finset.range N, ∑ j ∈ s,
            ∑ m ∈ Finset.range N, C (i,j) * Z (i,j) ^ n * W (i,j) ^ m := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.sum_comm]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
  have hfactor (N : ℕ) (i j : ι) :
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          C (i,j) * Z (i,j) ^ n * W (i,j) ^ m =
        C (i,j) * (∑ n ∈ Finset.range N, Z (i,j) ^ n) *
          (∑ m ∈ Finset.range N, W (i,j) ^ m) := by
    calc
      _ = ∑ n ∈ Finset.range N,
          (C (i,j) * Z (i,j) ^ n) * (∑ m ∈ Finset.range N, W (i,j) ^ m) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [Finset.mul_sum]
      _ = (∑ n ∈ Finset.range N, C (i,j) * Z (i,j) ^ n) *
          (∑ m ∈ Finset.range N, W (i,j) ^ m) := by
            rw [Finset.sum_mul]
      _ = _ := by
            congr 1
            rw [Finset.mul_sum]
  have hfun (N : ℕ) :
      ((↑((N : ℝ)⁻¹) : ℂ) ^ 2) *
          ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
            star (finiteTwoPhasePencil s c z w n m) *
              finiteTwoPhasePencil s c z w n m =
        ∑ p ∈ pairs, C p *
          ((↑((N : ℝ)⁻¹) : ℂ) * ∑ n ∈ Finset.range N, Z p ^ n) *
          ((↑((N : ℝ)⁻¹) : ℂ) * ∑ m ∈ Finset.range N, W p ^ m) := by
    calc
      _ = ((↑((N : ℝ)⁻¹) : ℂ) ^ 2) *
          ∑ i ∈ s, ∑ j ∈ s, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
            C (i,j) * Z (i,j) ^ n * W (i,j) ^ m := by
              congr 1
              simpa only [hexpand] using hreorder N
      _ = ∑ i ∈ s, ∑ j ∈ s, C (i,j) *
          ((↑((N : ℝ)⁻¹) : ℂ) * ∑ n ∈ Finset.range N, Z (i,j) ^ n) *
          ((↑((N : ℝ)⁻¹) : ℂ) * ∑ m ∈ Finset.range N, W (i,j) ^ m) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [hfactor]
              ring
      _ = ∑ p ∈ s.product s, C p *
          ((↑((N : ℝ)⁻¹) : ℂ) * ∑ n ∈ Finset.range N, Z p ^ n) *
          ((↑((N : ℝ)⁻¹) : ℂ) * ∑ m ∈ Finset.range N, W p ^ m) := by
              exact (Finset.sum_product s s
                (fun p => C p *
                  ((↑((N : ℝ)⁻¹) : ℂ) * ∑ n ∈ Finset.range N, Z p ^ n) *
                  ((↑((N : ℝ)⁻¹) : ℂ) * ∑ m ∈ Finset.range N, W p ^ m))).symm
      _ = _ := by rfl
  have htarget :
      (∑ p ∈ pairs, if Z p = 1 ∧ W p = 1 then C p else 0) =
        ∑ i ∈ s, star (c i) * c i := by
    calc
      _ = ∑ i ∈ s, ∑ j ∈ s,
          if Z (i,j) = 1 ∧ W (i,j) = 1 then C (i,j) else 0 := by
            change (∑ p ∈ s.product s,
              if Z p = 1 ∧ W p = 1 then C p else 0) = _
            exact Finset.sum_product s s
              (fun p => if Z p = 1 ∧ W p = 1 then C p else 0)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_eq_single i]
        · rw [if_pos ((hphase i i hi hi).2 rfl)]
        · intro j hj hji
          rw [if_neg]
          exact fun h => hji ((hphase i j hi hj).1 h).symm
        · intro hi'
          exact (hi' hi).elim
  rw [← htarget]
  exact hsum.congr' (Eventually.of_forall fun N => (hfun N).symm)

theorem tendsto_finiteTwoPhasePencil_cesaro_norm_sq
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c z w : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1) (hw : ∀ i ∈ s, ‖w i‖ = 1)
    (hinj : Set.InjOn (fun i => (z i, w i)) (s : Set ι)) :
    Tendsto
      (fun N : ℕ => ((N : ℝ)⁻¹ ^ 2) *
        ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          ‖finiteTwoPhasePencil s c z w n m‖ ^ 2)
      atTop (nhds (∑ i ∈ s, ‖c i‖ ^ 2)) := by
  have h := tendsto_finiteTwoPhasePencil_cesaro_star_mul s c z w hz hw hinj
  have hre := (Complex.continuous_re.tendsto _).comp h
  convert hre using 1
  · funext N
    rw [Function.comp_apply, Complex.mul_re]
    have hsre : (((↑((N : ℝ)⁻¹) : ℂ) ^ 2).re) = (N : ℝ)⁻¹ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have hsim : (((↑((N : ℝ)⁻¹) : ℂ) ^ 2).im) = 0 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_im]
    rw [hsre, hsim, zero_mul, sub_zero]
    congr 1
    rw [← Complex.reCLM_apply, map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [show star (finiteTwoPhasePencil s c z w n m) *
        finiteTwoPhasePencil s c z w n m =
        ((‖finiteTwoPhasePencil s c z w n m‖ ^ 2 : ℝ) : ℂ) by
      simpa using Complex.conj_mul' (finiteTwoPhasePencil s c z w n m)]
    exact Complex.ofReal_re _
  · apply congrArg nhds
    rw [← Complex.reCLM_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show star (c i) * c i = ((‖c i‖ ^ 2 : ℝ) : ℂ) by
      simpa using Complex.conj_mul' (c i)]
    exact Complex.ofReal_re _

/-! Two-prime horizontal source carrier. -/

def xiHorizontalPrimePhase (p : ℕ) (gamma : ℝ) : ℂ :=
  HTGeometry.phaseClockValue (Real.log p) (2 * gamma)

theorem burnolPrimeCharacter_mul_lineReflect_eq_horizontalPrimePhase
    {p : ℝ} (hp : 0 < p) (s : ℂ) :
    burnolPrimeCharacter p s * burnolPrimeCharacter p (lineReflect s) =
      HTGeometry.phaseClockValue (Real.log p) (2 * s.im) := by
  rw [burnolPrimeCharacter_eq_exp p hp, burnolPrimeCharacter_eq_exp p hp,
    ← Complex.exp_add]
  unfold lineReflect HTGeometry.phaseClockValue
  congr 1
  apply Complex.ext <;> simp
  <;> ring

theorem xiHorizontalPrimePhase_norm (p : ℕ) (gamma : ℝ) :
    ‖xiHorizontalPrimePhase p gamma‖ = 1 :=
  HTGeometry.norm_phaseClockValue _ _

theorem xiHorizontalPrimePhase_pair_injective :
    Function.Injective
      (fun gamma : ℝ => (xiHorizontalPrimePhase 2 gamma,
        xiHorizontalPrimePhase 3 gamma)) := by
  intro gamma delta h
  have hpair : primeLogPhaseClockPair 2 3 (2 * gamma) =
      primeLogPhaseClockPair 2 3 (2 * delta) := by
    simpa [xiHorizontalPrimePhase, primeLogPhaseClockPair,
      HTGeometry.phaseClockPair] using h
  have htime := primeLogPhaseClockPair_two_three_injective hpair
  linarith

def xiHorizontalCollisionTwoPrimeSourcePencil (T : ℝ) (a b : ℕ) : ℂ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset,
    ((analyticOrderAt xi rho).toNat : ℂ) *
      (burnolPrimeCharacter 2 rho * burnolPrimeCharacter 2 (lineReflect rho)) ^ a *
      (burnolPrimeCharacter 3 rho * burnolPrimeCharacter 3 (lineReflect rho)) ^ b

def xiHorizontalCollisionTwoPrimePhasePencil (T : ℝ) (a b : ℕ) : ℂ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset,
    ((analyticOrderAt xi rho).toNat : ℂ) *
      xiHorizontalPrimePhase 2 rho.im ^ a * xiHorizontalPrimePhase 3 rho.im ^ b

def xiHorizontalCollisionTwoPrimeGroupedPencil (T : ℝ) (a b : ℕ) : ℂ :=
  ∑ gamma ∈ (stripZeros_finite T).toFinset.image Complex.im,
    (xiHorizontalMultiplicity gamma : ℂ) *
      xiHorizontalPrimePhase 2 gamma ^ a * xiHorizontalPrimePhase 3 gamma ^ b

theorem xiHorizontalCollisionTwoPrimeSourcePencil_eq_phasePencil
    (T : ℝ) (a b : ℕ) :
    xiHorizontalCollisionTwoPrimeSourcePencil T a b =
      xiHorizontalCollisionTwoPrimePhasePencil T a b := by
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [burnolPrimeCharacter_mul_lineReflect_eq_horizontalPrimePhase (by norm_num),
    burnolPrimeCharacter_mul_lineReflect_eq_horizontalPrimePhase (by norm_num)]
  rfl

theorem xiHorizontalCollisionTwoPrimePhasePencil_eq_groupedPencil
    (T : ℝ) (a b : ℕ) :
    xiHorizontalCollisionTwoPrimePhasePencil T a b =
      xiHorizontalCollisionTwoPrimeGroupedPencil T a b := by
  classical
  let S := (stripZeros_finite T).toFinset
  let G := S.image Complex.im
  let m : ℂ → ℕ := fun rho => (analyticOrderAt xi rho).toNat
  let F : ℝ → ℂ := fun gamma =>
    xiHorizontalPrimePhase 2 gamma ^ a * xiHorizontalPrimePhase 3 gamma ^ b
  unfold xiHorizontalCollisionTwoPrimePhasePencil
    xiHorizontalCollisionTwoPrimeGroupedPencil
  simp_rw [mul_assoc]
  change (∑ rho ∈ S, (m rho : ℂ) * F rho.im) =
    ∑ gamma ∈ G, (xiHorizontalMultiplicity gamma : ℂ) * F gamma
  rw [eq_comm]
  calc
    (∑ gamma ∈ G, (xiHorizontalMultiplicity gamma : ℂ) * F gamma) =
        ∑ gamma ∈ G,
          (∑ rho ∈ S.filter (fun z => z.im = gamma), (m rho : ℂ)) * F gamma := by
            apply Finset.sum_congr rfl
            intro gamma hgamma
            rw [horizontalMultiplicity_eq_sum_stripZeros_filter_im hgamma]
            push_cast
            rfl
    _ = ∑ gamma ∈ G,
        ∑ rho ∈ S.filter (fun z => z.im = gamma), (m rho : ℂ) * F gamma := by
          apply Finset.sum_congr rfl
          intro gamma hgamma
          rw [Finset.sum_mul]
    _ = ∑ gamma ∈ G,
        ∑ rho ∈ S.filter (fun z => z.im = gamma), (m rho : ℂ) * F rho.im := by
          apply Finset.sum_congr rfl
          intro gamma hgamma
          apply Finset.sum_congr rfl
          intro rho hrho
          rw [(Finset.mem_filter.mp hrho).2]
    _ = ∑ rho ∈ S, (m rho : ℂ) * F rho.im := by
          exact Finset.sum_fiberwise_of_maps_to
            (fun rho hrho => Finset.mem_image.mpr ⟨rho, hrho, rfl⟩)
            (fun rho => (m rho : ℂ) * F rho.im)

theorem xiHorizontalCollisionTwoPrimeSourcePencil_eq_groupedPencil
    (T : ℝ) (a b : ℕ) :
    xiHorizontalCollisionTwoPrimeSourcePencil T a b =
      xiHorizontalCollisionTwoPrimeGroupedPencil T a b := by
  rw [xiHorizontalCollisionTwoPrimeSourcePencil_eq_phasePencil,
    xiHorizontalCollisionTwoPrimePhasePencil_eq_groupedPencil]

theorem tendsto_xiHorizontalCollisionTwoPrimeSourcePencil_cesaro_norm_sq
    (T : ℝ) :
    Tendsto
      (fun N : ℕ => ((N : ℝ)⁻¹ ^ 2) *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
          ‖xiHorizontalCollisionTwoPrimeSourcePencil T a b‖ ^ 2)
      atTop (nhds (xiStripWindowHorizontalSquareSum T : ℝ)) := by
  let G := (stripZeros_finite T).toFinset.image Complex.im
  have hlim := tendsto_finiteTwoPhasePencil_cesaro_norm_sq G
    (fun gamma => (xiHorizontalMultiplicity gamma : ℂ))
    (xiHorizontalPrimePhase 2) (xiHorizontalPrimePhase 3)
    (fun gamma _ => xiHorizontalPrimePhase_norm 2 gamma)
    (fun gamma _ => xiHorizontalPrimePhase_norm 3 gamma)
    xiHorizontalPrimePhase_pair_injective.injOn
  convert hlim using 1
  · funext N
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [xiHorizontalCollisionTwoPrimeSourcePencil_eq_groupedPencil]
    rfl
  · apply congrArg nhds
    rw [xiStripWindowHorizontalSquareSum]
    push_cast
    apply Finset.sum_congr rfl
    intro gamma hgamma
    simp

/-- Centered two-prime source energy.  Local divisor squares are removed before taking the
two-clock Cesàro limit, so only horizontal collisions survive. -/
def xiHorizontalCollisionTwoPrimeSourceExcess (T : ℝ) (N : ℕ) : ℝ :=
  ((N : ℝ)⁻¹ ^ 2) *
      ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
        ‖xiHorizontalCollisionTwoPrimeSourcePencil T a b‖ ^ 2 -
    xiStripWindowLocalSquareSum T

theorem tendsto_xiHorizontalCollisionTwoPrimeSourceExcess
    (T : ℝ) :
    Tendsto (xiHorizontalCollisionTwoPrimeSourceExcess T) atTop
      (nhds (xiHorizontalCollisionCharge T : ℝ)) := by
  have hconst : Tendsto (fun _ : ℕ => (xiStripWindowLocalSquareSum T : ℝ))
      atTop (nhds (xiStripWindowLocalSquareSum T : ℝ)) := tendsto_const_nhds
  have hlim :=
    (tendsto_xiHorizontalCollisionTwoPrimeSourcePencil_cesaro_norm_sq T).sub
      hconst
  convert hlim using 1
  · rfl
  · apply congrArg nhds
    rw [xiStripWindowHorizontalSquareSum_eq_localSquare_add_collisionCharge]
    push_cast
    ring

/-- Exact source formulation of RH: every finite-window two-prime source excess converges to
zero.  This is coefficient-faithful and uses both critical-line reflection orientations. -/
theorem riemannHypothesis_iff_twoPrimeSourceExcess_tendsto_zero :
    RiemannHypothesis ↔
      ∀ T : ℝ, Tendsto (xiHorizontalCollisionTwoPrimeSourceExcess T)
        atTop (nhds 0) := by
  constructor
  · intro hRH T
    simpa [xiHorizontalCollisionCharge_eq_zero_of_riemannHypothesis hRH T] using
      tendsto_xiHorizontalCollisionTwoPrimeSourceExcess T
  · intro hsource
    apply riemannHypothesis_iff_forall_horizontalCollisionCharge_eq_zero.mpr
    intro T
    have hzero : (xiHorizontalCollisionCharge T : ℝ) = 0 :=
      tendsto_nhds_unique
        (tendsto_xiHorizontalCollisionTwoPrimeSourceExcess T) (hsource T)
    exact_mod_cast hzero

/-- The precise strict source estimate needed by the quantized endpoint.  A merely normalized
`o(N(T))` estimate cannot replace this absolute bound below the two-unit collision quantum. -/
theorem riemannHypothesis_of_twoPrimeSourceExcess_eventually_bounded_lt_two
    (hsource : ∀ T : ℝ, ∃ C : ℝ, C < 2 ∧
      ∀ᶠ N : ℕ in atTop, xiHorizontalCollisionTwoPrimeSourceExcess T N ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_forall_horizontalCollisionCharge_lt_two.mpr
  intro T
  obtain ⟨C, hC, hbound⟩ := hsource T
  have hle : (xiHorizontalCollisionCharge T : ℝ) ≤ C :=
    le_of_tendsto (tendsto_xiHorizontalCollisionTwoPrimeSourceExcess T) hbound
  have hlt : (xiHorizontalCollisionCharge T : ℝ) < 2 := hle.trans_lt hC
  exact_mod_cast hlt

/-- Conversely, RH supplies the strict absolute source bound (take any constant between zero and
two). Thus this is an equivalent source-side endpoint, not an extra conditional assumption. -/
theorem riemannHypothesis_iff_twoPrimeSourceExcess_eventually_bounded_lt_two :
    RiemannHypothesis ↔
      ∀ T : ℝ, ∃ C : ℝ, C < 2 ∧
        ∀ᶠ N : ℕ in atTop,
          xiHorizontalCollisionTwoPrimeSourceExcess T N ≤ C := by
  constructor
  · intro hRH T
    refine ⟨1, by norm_num, ?_⟩
    have hlim : Tendsto (xiHorizontalCollisionTwoPrimeSourceExcess T)
        atTop (nhds 0) :=
      riemannHypothesis_iff_twoPrimeSourceExcess_tendsto_zero.mp hRH T
    filter_upwards [hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with N hN
    exact hN.le
  · exact riemannHypothesis_of_twoPrimeSourceExcess_eventually_bounded_lt_two

end
end RHTower

