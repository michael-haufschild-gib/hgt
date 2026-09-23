import GaloisForLFunctions.HTGeometry.ProjectiveHorizonBinomialPoleCone
import GaloisForLFunctions.HTGeometry.GammaSimpleZeroBellHorizonAnalytic
import GaloisForLFunctions.HTGeometry.ShiftedMonomialJet
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentJet
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonAllRankQSystem
import GaloisForLFunctions.HTGeometry.AffineReflectionJet

/-!
# Finite-width caustic pole cones at analytic zeros

For a holomorphic source with a zero of exact order `r`, this module proves that its rectangular
reciprocal-square Toeplitz caustic of rank `m` and positive depth `n` has full pole order `-m*n`
exactly when `m ≤ 2*r`. It recovers `2*r` as the greatest full-pole rank and proves strict order
improvement beyond the cone.

The same construction supplies unconditional all-rank Q-system infrastructure, exact reflection
parity, odd-area vanishing at `1/2`, and the unique horizontal tropical continuation at the cone
boundary. All analytic order statements are derived from coefficientwise normalized limits and
meromorphic germs; no nonvanishing or hypertranscendence premise is used for the pole cutoff.
-/

open Filter Topology Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Rectangular horizon determinants commute with coefficient-ring homomorphisms. -/
theorem horizonAmplitude_map
    {R S : Type*} [CommRing R] [CommRing S] (phi : R →+* S)
    (h : ℕ → R) (m n : ℕ) :
    phi (horizonAmplitude h m n) =
      horizonAmplitude (fun k => phi (h k)) m n := by
  rw [horizonAmplitude, horizonAmplitude, phi.map_det]
  congr 1
  ext i j
  simp [rectangularSchurToeplitz]
  split_ifs <;> simp

/-- Unconditional all-rank rectangular Q-system.  The universal polynomial identity is proved in
the fraction field, where the already-established nonzero-center identity applies, and then
specialized back to every characteristic-zero field. -/
theorem horizonAmplitude_qSystem
    {K : Type*} [Field K] [CharZero K] (h : ℕ → K)
    (c n : ℕ) (hn : 0 < n) :
    horizonAmplitude h (c + 1) n ^ 2 =
      horizonAmplitude h (c + 1) (n - 1) *
          horizonAmplitude h (c + 1) (n + 1) +
        horizonAmplitude h c n * horizonAmplitude h (c + 2) n := by
  let R := MvPolynomial ℕ ℚ
  let L := FractionRing R
  let iota : R →+* L := algebraMap R L
  let X : ℕ → R := MvPolynomial.X
  let XL : ℕ → L := fun k => iota (X k)
  have hiota : Function.Injective iota := by
    simpa [iota] using IsFractionRing.injective R L
  have hcenterR : horizonAmplitude X c n ≠ 0 := by
    simpa [R, X, horizonAmplitudePolynomial] using
      horizonAmplitudePolynomial_ne_zero ℚ c n
  have hcenterL : horizonAmplitude XL c n ≠ 0 := by
    intro hz
    apply hcenterR
    apply hiota
    rw [map_zero, horizonAmplitude_map]
    exact hz
  have hqL := horizonAmplitude_qSystem_of_center_ne_zero XL c n hn hcenterL
  have hqR :
      horizonAmplitude X (c + 1) n ^ 2 =
        horizonAmplitude X (c + 1) (n - 1) *
            horizonAmplitude X (c + 1) (n + 1) +
          horizonAmplitude X c n * horizonAmplitude X (c + 2) n := by
    apply hiota
    simp only [map_pow, map_mul, map_add]
    rw [horizonAmplitude_map, horizonAmplitude_map, horizonAmplitude_map,
      horizonAmplitude_map, horizonAmplitude_map]
    exact hqL
  let ev : R →+* K := (MvPolynomial.aeval h).toRingHom
  have hev := congrArg ev hqR
  simp only [map_pow, map_mul, map_add] at hev
  rw [horizonAmplitude_map, horizonAmplitude_map, horizonAmplitude_map,
    horizonAmplitude_map, horizonAmplitude_map] at hev
  simpa [ev, R, X] using hev

theorem rectangularSchurToeplitz_scaled_det {K : Type*} [Field K]
    (h : ℕ → K) (u : K) (n m : ℕ) (hu : u ≠ 0) :
    (rectangularSchurToeplitz (fun k => u ^ k * h k) n m).det =
      u ^ (m * n) * (rectangularSchurToeplitz h n m).det := by
  let P : K := ∏ i : Fin m, u ^ (i : ℕ)
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ hu
  have hmat : rectangularSchurToeplitz (fun k => u ^ k * h k) n m =
      u ^ n • (diagonal (fun r : Fin m => u ^ (r : ℕ)) *
        rectangularSchurToeplitz h n m *
        diagonal (fun i : Fin m => (u⁻¹) ^ (i : ℕ))) := by
    ext r i
    rw [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [rectangularSchurToeplitz]
    split_ifs with hi
    · simp only [smul_eq_mul]
      have hui : u ^ (i : ℕ) ≠ 0 := pow_ne_zero _ hu
      rw [inv_pow]
      field_simp [hui]
      calc
        u ^ (n + (r : ℕ) - (i : ℕ)) * h (n + (r : ℕ) - (i : ℕ)) * u ^ (i : ℕ) =
            (u ^ (n + (r : ℕ) - (i : ℕ)) * u ^ (i : ℕ)) *
              h (n + (r : ℕ) - (i : ℕ)) := by ring
        _ = u ^ ((n + (r : ℕ) - (i : ℕ)) + (i : ℕ)) *
              h (n + (r : ℕ) - (i : ℕ)) := by rw [pow_add]
        _ = u ^ (n + (r : ℕ)) * h (n + (r : ℕ) - (i : ℕ)) := by
              rw [Nat.sub_add_cancel hi]
        _ = h (n + (r : ℕ) - (i : ℕ)) * u ^ n * u ^ (r : ℕ) := by
              rw [pow_add]
              ring
    · simp
  rw [hmat, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul]
  simp only [Matrix.det_diagonal, Fintype.card_fin]
  have hinvprod : (∏ i : Fin m, (u⁻¹) ^ (i : ℕ)) = P⁻¹ := by
    simp only [← inv_pow, ← Finset.prod_inv_distrib, P]
  rw [hinvprod]
  rw [← pow_mul]
  rw [show u ^ (n * m) = u ^ (m * n) from congrArg (u ^ ·) (Nat.mul_comm n m)]
  field_simp
  ring

theorem tendsto_det_rectangularSchurToeplitz_of_tendsto
    {l : Filter ℂ} {a : ℕ → ℂ → ℂ} {c : ℕ → ℂ} (n m : ℕ)
    (ha : ∀ k, Tendsto (a k) l (nhds (c k))) :
    Tendsto (fun z => (rectangularSchurToeplitz (fun k => a k z) n m).det) l
      (nhds (rectangularSchurToeplitz c n m).det) := by
  have hmatrix : Tendsto
      (fun z => rectangularSchurToeplitz (fun k => a k z) n m) l
      (nhds (rectangularSchurToeplitz c n m)) := by
    change Tendsto
      (fun z => fun i j => rectangularSchurToeplitz (fun k => a k z) n m i j) l
      (nhds (fun i j => rectangularSchurToeplitz c n m i j))
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_pi_nhds]
    intro j
    simp only [rectangularSchurToeplitz]
    split_ifs
    · exact ha _
    · exact tendsto_const_nhds
  change Tendsto
    ((fun M : Matrix (Fin m) (Fin m) ℂ => M.det) ∘
      fun z => rectangularSchurToeplitz (fun k => a k z) n m) l
      (nhds (rectangularSchurToeplitz c n m).det)
  exact continuous_id.matrix_det.continuousAt.tendsto.comp hmatrix

theorem PowerSeries.rescale_inv {K : Type*} [Field K]
    (u : K) (P : PowerSeries K) (hP : PowerSeries.constantCoeff P ≠ 0) :
    PowerSeries.rescale u P⁻¹ = (PowerSeries.rescale u P)⁻¹ := by
  symm
  apply (PowerSeries.inv_eq_iff_mul_eq_one ?_).2
  · rw [← map_mul]
    simpa using congrArg (PowerSeries.rescale u) (PowerSeries.inv_mul_cancel P hP)
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale]
    norm_num
    exact hP

def normalizedAnalyticJetSeries (f : ℂ → ℂ) (s : ℂ) : PowerSeries ℂ :=
  PowerSeries.C (f s)⁻¹ * GaloisForLFunctions.analyticJetPowerSeries f s

theorem normalizedAnalyticJetSeries_constantCoeff {f : ℂ → ℂ} {s : ℂ}
    (hfs : f s ≠ 0) :
    PowerSeries.constantCoeff (normalizedAnalyticJetSeries f s) = 1 := by
  simp [normalizedAnalyticJetSeries, GaloisForLFunctions.analyticJetPowerSeries, hfs]

def causticReciprocalSquareCoeff (f : ℂ → ℂ) (s : ℂ) (k : ℕ) : ℂ :=
  PowerSeries.coeff k ((normalizedAnalyticJetSeries f s)⁻¹ ^ 2)

def causticTau (f : ℂ → ℂ) (n m : ℕ) (s : ℂ) : ℂ :=
  (rectangularSchurToeplitz (causticReciprocalSquareCoeff f s) n m).det

theorem scaled_causticReciprocalSquareCoeff {f : ℂ → ℂ} {s u : ℂ}
    (hfs : f s ≠ 0) (k : ℕ) :
    u ^ k * causticReciprocalSquareCoeff f s k =
      PowerSeries.coeff k ((PowerSeries.rescale u (normalizedAnalyticJetSeries f s))⁻¹ ^ 2) := by
  calc
    u ^ k * causticReciprocalSquareCoeff f s k =
        PowerSeries.coeff k (PowerSeries.rescale u ((normalizedAnalyticJetSeries f s)⁻¹ ^ 2)) := by
          exact (PowerSeries.coeff_rescale _ _ _).symm
    _ = PowerSeries.coeff k ((PowerSeries.rescale u (normalizedAnalyticJetSeries f s))⁻¹ ^ 2) := by
      rw [map_pow, PowerSeries.rescale_inv u (normalizedAnalyticJetSeries f s) (by
        rw [normalizedAnalyticJetSeries_constantCoeff hfs]
        exact one_ne_zero)]

theorem coeff_rescale_normalizedAnalyticJetSeries
    (g : ℂ → ℂ) (s u : ℂ) (j : ℕ) :
    PowerSeries.coeff j (PowerSeries.rescale u (normalizedAnalyticJetSeries g s)) =
      u ^ j * ((g s)⁻¹ * (((j.factorial : ℂ)⁻¹) * iteratedDeriv j g s)) := by
  rw [PowerSeries.coeff_rescale]
  congr 1
  rw [normalizedAnalyticJetSeries, PowerSeries.coeff_mul]
  rw [Finset.sum_eq_single (0, j)]
  · simp [GaloisForLFunctions.analyticJetPowerSeries]
  · rintro ⟨a, b⟩ hab hne
    have habsum : a + b = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    by_cases ha : a = 0
    · subst a
      have hb : b = j := by omega
      exact (hne (by simp [hb])).elim
    · simp [PowerSeries.coeff_C, ha]
  · simp

theorem tendsto_coeff_rescale_normalizedAnalyticJetSeries_unit
    {g : ℂ → ℂ} {rho : ℂ} (hg : AnalyticAt ℂ g rho) (hgrho : g rho ≠ 0)
    (j : ℕ) :
    Tendsto
      (fun u => PowerSeries.coeff j
        (PowerSeries.rescale u (normalizedAnalyticJetSeries g (rho + u))))
      (nhds 0) (nhds (if j = 0 then 1 else 0)) := by
  have hshift : Tendsto (fun u : ℂ => rho + u) (nhds 0) (nhds rho) :=
    by
      have hc : Tendsto (fun _ : ℂ => rho) (nhds 0) (nhds rho) := tendsto_const_nhds
      have hi : Tendsto (fun u : ℂ => u) (nhds 0) (nhds 0) := tendsto_id
      simpa using hc.add hi
  have hgval : Tendsto (fun u => g (rho + u)) (nhds 0) (nhds (g rho)) :=
    hg.continuousAt.tendsto.comp hshift
  have hgderiv : Tendsto (fun u => iteratedDeriv j g (rho + u)) (nhds 0)
      (nhds (iteratedDeriv j g rho)) :=
    (GaloisForLFunctions.analyticAt_iteratedDeriv_of_analyticAt hg j).continuousAt.tendsto.comp
      hshift
  rw [show (fun u => PowerSeries.coeff j
      (PowerSeries.rescale u (normalizedAnalyticJetSeries g (rho + u)))) =
      fun u => u ^ j * ((g (rho + u))⁻¹ *
        (((j.factorial : ℂ)⁻¹) * iteratedDeriv j g (rho + u))) by
        funext u
        exact coeff_rescale_normalizedAnalyticJetSeries g (rho + u) u j]
  by_cases hj : j = 0
  · subst j
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero,
      one_mul]
    have hlim := hgval.inv₀ hgrho
    simpa [inv_mul_cancel₀ hgrho] using hlim.mul hgval
  · have hid : Tendsto (fun u : ℂ => u) (nhds 0) (nhds 0) := tendsto_id
    have hpow : Tendsto (fun u : ℂ => u ^ j) (nhds 0) (nhds 0) := by
      simpa [zero_pow hj] using hid.pow j
    have hfac : Tendsto (fun _ : ℂ => ((j.factorial : ℂ)⁻¹)) (nhds 0)
        (nhds ((j.factorial : ℂ)⁻¹)) := tendsto_const_nhds
    have hrest : Tendsto
        (fun u => (g (rho + u))⁻¹ * (((j.factorial : ℂ)⁻¹) *
          iteratedDeriv j g (rho + u))) (nhds 0)
        (nhds ((g rho)⁻¹ * (((j.factorial : ℂ)⁻¹) * iteratedDeriv j g rho))) :=
      (hgval.inv₀ hgrho).mul (hfac.mul hgderiv)
    simpa [hj] using hpow.mul hrest

def binomialUnitPowerSeries (r : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun j => (Nat.choose r j : ℂ)

@[simp]
theorem binomialUnitPowerSeries_coeff (r j : ℕ) :
    PowerSeries.coeff j (binomialUnitPowerSeries r) = (Nat.choose r j : ℂ) := by
  simp [binomialUnitPowerSeries]

theorem inv_factorial_mul_descFactorial (r j : ℕ) :
    ((j.factorial : ℂ)⁻¹) * (r.descFactorial j : ℂ) = (Nat.choose r j : ℂ) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp [hj]

theorem rescale_normalized_shiftedMonomialSeries (rho u : ℂ) (r : ℕ) (hu : u ≠ 0) :
    PowerSeries.rescale u
      (normalizedAnalyticJetSeries (fun z => (z - rho) ^ r) (rho + u)) =
      binomialUnitPowerSeries r := by
  apply PowerSeries.ext
  intro j
  rw [coeff_rescale_normalizedAnalyticJetSeries, binomialUnitPowerSeries_coeff]
  have hd := GaloisForLFunctions.HTGeometry.iterate_deriv_const_mul_sub_pow rho j 1 r
  simp only [one_mul] at hd
  rw [iteratedDeriv_eq_iterate, hd]
  simp only [add_sub_cancel_left]
  by_cases hjr : j ≤ r
  · have hur : u ^ r ≠ 0 := pow_ne_zero _ hu
    rw [← mul_assoc ((j.factorial : ℂ)⁻¹)]
    rw [inv_factorial_mul_descFactorial]
    field_simp [hur]
    rw [show u ^ j * (Nat.choose r j : ℂ) * u ^ (r - j) =
      (u ^ j * u ^ (r - j)) * (Nat.choose r j : ℂ) by ring]
    rw [← pow_add, Nat.add_sub_of_le hjr]
  · have hdesc : r.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
    have hchoose : Nat.choose r j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hdesc, hchoose]
    simp

/-- Coefficientwise convergence of unit power series is preserved by formal inversion. -/
theorem tendsto_coeff_inv_of_tendsto_coeff
    {α : Type*} {l : Filter α} {P : α → PowerSeries ℂ} {Q : PowerSeries ℂ}
    (hP0 : ∀ a, PowerSeries.constantCoeff (P a) = 1)
    (hQ0 : PowerSeries.constantCoeff Q = 1)
    (hcoeff : ∀ j, Tendsto (fun a => PowerSeries.coeff j (P a)) l
      (nhds (PowerSeries.coeff j Q))) :
    ∀ k, Tendsto (fun a => PowerSeries.coeff k (P a)⁻¹) l
      (nhds (PowerSeries.coeff k Q⁻¹)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk : k = 0
      · subst k
        have hleft : (fun a => PowerSeries.coeff 0 (P a)⁻¹) = fun _ => 1 := by
          funext a
          rw [PowerSeries.coeff_inv]
          rw [if_pos rfl, hP0, inv_one]
        have hright : PowerSeries.coeff 0 Q⁻¹ = 1 := by
          rw [PowerSeries.coeff_inv]
          rw [if_pos rfl, hQ0, inv_one]
        rw [hleft, hright]
        exact tendsto_const_nhds
      · have hsum : Tendsto
            (fun a => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) k,
              if x.2 < k then
                PowerSeries.coeff x.1 (P a) * PowerSeries.coeff x.2 (P a)⁻¹
              else 0) l
            (nhds (∑ x ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) k,
              if x.2 < k then
                PowerSeries.coeff x.1 Q * PowerSeries.coeff x.2 Q⁻¹
              else 0)) := by
          apply tendsto_finsetSum
          intro x hx
          by_cases hxk : x.2 < k
          · simpa [hxk] using (hcoeff x.1).mul (ih x.2 hxk)
          · simp only [hxk, if_false]
            exact tendsto_const_nhds
        have hleft : (fun a => PowerSeries.coeff k (P a)⁻¹) =
            fun a => -(∑ x ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) k,
              if x.2 < k then
                PowerSeries.coeff x.1 (P a) * PowerSeries.coeff x.2 (P a)⁻¹
              else 0) := by
          funext a
          rw [PowerSeries.coeff_inv]
          rw [if_neg hk, hP0, inv_one, neg_one_mul]
        have hright : PowerSeries.coeff k Q⁻¹ =
            -(∑ x ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) k,
              if x.2 < k then
                PowerSeries.coeff x.1 Q * PowerSeries.coeff x.2 Q⁻¹
              else 0) := by
          rw [PowerSeries.coeff_inv]
          rw [if_neg hk, hQ0, inv_one, neg_one_mul]
        rw [hleft, hright]
        exact hsum.neg

/-- Coefficientwise convergence of unit power series is preserved by inverse squaring. -/
theorem tendsto_coeff_inv_sq_of_tendsto_coeff
    {α : Type*} {l : Filter α} {P : α → PowerSeries ℂ} {Q : PowerSeries ℂ}
    (hP0 : ∀ a, PowerSeries.constantCoeff (P a) = 1)
    (hQ0 : PowerSeries.constantCoeff Q = 1)
    (hcoeff : ∀ j, Tendsto (fun a => PowerSeries.coeff j (P a)) l
      (nhds (PowerSeries.coeff j Q))) (k : ℕ) :
    Tendsto (fun a => PowerSeries.coeff k ((P a)⁻¹ ^ 2)) l
      (nhds (PowerSeries.coeff k (Q⁻¹ ^ 2))) := by
  have hinv := tendsto_coeff_inv_of_tendsto_coeff hP0 hQ0 hcoeff
  simp only [pow_two, PowerSeries.coeff_mul]
  apply tendsto_finsetSum
  intro x hx
  exact (hinv x.1).mul (hinv x.2)

/-- Multiplication by a coefficientwise vanishing normalized unit tends to the fixed factor. -/
theorem tendsto_coeff_mul_unit
    {α : Type*} {l : Filter α} (B : PowerSeries ℂ) (U : α → PowerSeries ℂ)
    (hU : ∀ j, Tendsto (fun a => PowerSeries.coeff j (U a)) l
      (nhds (if j = 0 then 1 else 0))) (k : ℕ) :
    Tendsto (fun a => PowerSeries.coeff k (B * U a)) l
      (nhds (PowerSeries.coeff k B)) := by
  have hU' : ∀ j, Tendsto (fun a => PowerSeries.coeff j (U a)) l
      (nhds (PowerSeries.coeff j (1 : PowerSeries ℂ))) := by
    intro j
    simpa [PowerSeries.coeff_one] using hU j
  have hsum : Tendsto
      (fun a => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) k,
        PowerSeries.coeff x.1 B * PowerSeries.coeff x.2 (U a)) l
      (nhds (∑ x ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) k,
        PowerSeries.coeff x.1 B * PowerSeries.coeff x.2 (1 : PowerSeries ℂ))) := by
    apply tendsto_finsetSum
    intro x hx
    exact tendsto_const_nhds.mul (hU' x.2)
  have hfun : (fun a => PowerSeries.coeff k (B * U a)) =
      fun a => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) k,
        PowerSeries.coeff x.1 B * PowerSeries.coeff x.2 (U a) := by
    funext a
    rw [PowerSeries.coeff_mul]
  have hlim : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) k,
        PowerSeries.coeff x.1 B * PowerSeries.coeff x.2 (1 : PowerSeries ℂ)) =
      PowerSeries.coeff k B := by
    rw [← PowerSeries.coeff_mul]
    simp
  rw [hfun]
  simpa only [hlim] using hsum

/-- Global representative of the nonvanishing local factor at an exact analytic zero. -/
theorem exists_global_factor_of_analyticOrderAt_eq_natCast
    {f : ℂ → ℂ} {rho : ℂ} {r : ℕ} (hf : AnalyticAt ℂ f rho) (hr : 1 ≤ r)
    (horder : analyticOrderAt f rho = r) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g rho ∧ g rho ≠ 0 ∧
      ∀ z, f z = (z - rho) ^ r * g z := by
  obtain ⟨g, hg, hgrho, hfactor⟩ := (hf.analyticOrderAt_eq_natCast).1 horder
  simp only [smul_eq_mul] at hfactor
  let G : ℂ → ℂ := fun z => if z = rho then g z else f z / (z - rho) ^ r
  have hG : g =ᶠ[nhds rho] G := by
    filter_upwards [hfactor] with z hz
    by_cases hzr : z = rho
    · simp [G, hzr]
    · simp only [G, hzr, if_false]
      rw [hz]
      field_simp [pow_ne_zero r (sub_ne_zero.mpr hzr)]
  have hfrho : f rho = 0 := by
    have h := hfactor.self_of_nhds
    simpa [Nat.ne_of_gt hr] using h
  refine ⟨G, hg.congr hG, ?_, ?_⟩
  · simpa [G] using hgrho
  · intro z
    by_cases hzr : z = rho
    · subst z
      simpa [G, Nat.ne_of_gt hr] using hfrho
    · simp only [G, hzr, if_false]
      field_simp [pow_ne_zero r (sub_ne_zero.mpr hzr)]

/-- Normalized analytic jets turn products into products. -/
theorem normalizedAnalyticJetSeries_mul
    {f g : ℂ → ℂ} {s : ℂ}
    (hf : ∀ n : ℕ, ContDiffAt ℂ n f s)
    (hg : ∀ n : ℕ, ContDiffAt ℂ n g s) :
    normalizedAnalyticJetSeries (f * g) s =
      normalizedAnalyticJetSeries f s * normalizedAnalyticJetSeries g s := by
  rw [normalizedAnalyticJetSeries, normalizedAnalyticJetSeries,
    normalizedAnalyticJetSeries, GaloisForLFunctions.analyticJetPowerSeries_mul hf hg]
  simp only [Pi.mul_apply, _root_.mul_inv_rev]
  rw [map_mul]
  ac_rfl

/-- Near a factored zero, the rescaled normalized jet splits into binomial and unit factors. -/
theorem eventually_rescale_normalized_factorization
    {f g : ℂ → ℂ} {rho : ℂ} {r : ℕ}
    (hg : AnalyticAt ℂ g rho)
    (hfactor : ∀ z, f z = (z - rho) ^ r * g z) :
    ∀ᶠ u in nhdsWithin 0 ({0}ᶜ : Set ℂ),
      PowerSeries.rescale u (normalizedAnalyticJetSeries f (rho + u)) =
        binomialUnitPowerSeries r *
          PowerSeries.rescale u (normalizedAnalyticJetSeries g (rho + u)) := by
  have hshift : Tendsto (fun u : ℂ => rho + u) (nhdsWithin 0 ({0}ᶜ : Set ℂ))
      (nhds rho) := by
    have hc : Tendsto (fun _ : ℂ => rho) (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds rho) :=
      tendsto_const_nhds
    have hi : Tendsto (fun u : ℂ => u) (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds 0) :=
      tendsto_id.mono_left inf_le_left
    simpa using hc.add hi
  have hgan : ∀ᶠ u in nhdsWithin 0 ({0}ᶜ : Set ℂ), AnalyticAt ℂ g (rho + u) :=
    hshift.eventually hg.eventually_analyticAt
  have hune : ∀ᶠ u in nhdsWithin 0 ({0}ᶜ : Set ℂ), u ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hu
  filter_upwards [hgan, hune] with u hgu hu
  have hfun : f = (fun z => (z - rho) ^ r) * g := by
    funext z
    simpa only [Pi.mul_apply] using hfactor z
  have hmono : ∀ n : ℕ, ContDiffAt ℂ n (fun z : ℂ => (z - rho) ^ r) (rho + u) := by
    intro n
    exact ((analyticAt_id.sub analyticAt_const).pow r).contDiffAt
  rw [hfun, normalizedAnalyticJetSeries_mul hmono (fun n => hgu.contDiffAt), map_mul,
    rescale_normalized_shiftedMonomialSeries rho u r hu]

/-- Every rescaled normalized jet coefficient tends to its binomial zero-model coefficient. -/
theorem tendsto_coeff_rescale_normalized_factorization
    {f g : ℂ → ℂ} {rho : ℂ} {r : ℕ}
    (hg : AnalyticAt ℂ g rho) (hgrho : g rho ≠ 0)
    (hfactor : ∀ z, f z = (z - rho) ^ r * g z) (j : ℕ) :
    Tendsto
      (fun u => PowerSeries.coeff j
        (PowerSeries.rescale u (normalizedAnalyticJetSeries f (rho + u))))
      (nhdsWithin 0 ({0}ᶜ : Set ℂ))
      (nhds (PowerSeries.coeff j (binomialUnitPowerSeries r))) := by
  let U : ℂ → PowerSeries ℂ := fun u =>
    PowerSeries.rescale u (normalizedAnalyticJetSeries g (rho + u))
  have hU : ∀ k, Tendsto (fun u => PowerSeries.coeff k (U u))
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds (if k = 0 then 1 else 0)) := by
    intro k
    exact (tendsto_coeff_rescale_normalizedAnalyticJetSeries_unit hg hgrho k).mono_left
      inf_le_left
  have hlim := tendsto_coeff_mul_unit (binomialUnitPowerSeries r) U hU j
  apply hlim.congr'
  filter_upwards [eventually_rescale_normalized_factorization hg hfactor] with u hu
  rw [hu]

theorem binomialUnitPowerSeries_succ (r : ℕ) :
    binomialUnitPowerSeries (r + 1) =
      binomialUnitPowerSeries r * (1 + PowerSeries.X) := by
  ext k
  cases k with
  | zero => simp [binomialUnitPowerSeries, PowerSeries.coeff_mul]
  | succ k =>
      rw [mul_add]
      simp only [mul_one, map_add]
      rw [← pow_one PowerSeries.X,
        PowerSeries.coeff_mul_X_pow (binomialUnitPowerSeries r) 1 k]
      simp [binomialUnitPowerSeries, Nat.choose_succ_succ, add_comm]

theorem binomialUnitPowerSeries_eq_one_add_X_pow (r : ℕ) :
    binomialUnitPowerSeries r = (1 + PowerSeries.X) ^ r := by
  induction r with
  | zero =>
      ext k
      cases k <;> simp [binomialUnitPowerSeries]
  | succ r ih =>
      rw [binomialUnitPowerSeries_succ, ih, pow_succ]

theorem rescale_neg_one_one_sub_X_hypertranscendentalCausticDivisorPoleCone :
    PowerSeries.rescale (-1 : ℂ) (1 - PowerSeries.X) = 1 + PowerSeries.X := by
  rw [map_sub, map_one, PowerSeries.rescale_X]
  norm_num

theorem invOneSubPow_val_eq_inv_pow (p : ℕ) :
    (↑(PowerSeries.invOneSubPow ℂ p) : PowerSeries ℂ) =
      (1 - PowerSeries.X)⁻¹ ^ p := by
  rw [PowerSeries.invOneSubPow_eq_inv_one_sub_pow]
  rw [Units.val_pow_eq_pow_val]
  congr 1
  symm
  apply (PowerSeries.inv_eq_iff_mul_eq_one (by simp)).2
  exact Units.inv_val _

theorem inv_pow_one_add_X_eq_rescale_invOneSubPow (p : ℕ) :
    (1 + PowerSeries.X : PowerSeries ℂ)⁻¹ ^ p =
      PowerSeries.rescale (-1 : ℂ) (↑(PowerSeries.invOneSubPow ℂ p) : PowerSeries ℂ) := by
  rw [← rescale_neg_one_one_sub_X_hypertranscendentalCausticDivisorPoleCone]
  rw [← PowerSeries.rescale_inv (-1 : ℂ) (1 - PowerSeries.X) (by simp), ← map_pow,
    invOneSubPow_val_eq_inv_pow]

theorem coeff_inv_pow_one_add_X_eq_complexSignedPoleConeCoeff
    (p k : ℕ) (hp : 1 ≤ p) :
    PowerSeries.coeff k ((1 + PowerSeries.X : PowerSeries ℂ)⁻¹ ^ p) =
      complexSignedPoleConeCoeff p k := by
  rw [inv_pow_one_add_X_eq_rescale_invOneSubPow, PowerSeries.coeff_rescale]
  have hp' : p = (p - 1) + 1 := by omega
  have hseries : (↑(PowerSeries.invOneSubPow ℂ p) : PowerSeries ℂ) =
      PowerSeries.mk (fun n => (Nat.choose (p - 1 + n) (p - 1) : ℂ)) := by
    nth_rewrite 1 [hp']
    exact PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose ℂ (p - 1)
  rw [hseries]
  simp only [PowerSeries.coeff_mk, complexSignedPoleConeCoeff]
  congr 2
  have hchoose : Nat.choose (p - 1 + k) (p - 1) = Nat.choose (p + k - 1) k := by
    calc
      Nat.choose (p - 1 + k) (p - 1) = Nat.choose (p - 1 + k) k := by
        calc
          _ = Nat.choose (p - 1 + k) (p - 1 + k - (p - 1)) :=
            (@Nat.choose_symm (p - 1 + k) (p - 1) (by omega)).symm
          _ = Nat.choose (p - 1 + k) k := by congr 2; omega
      _ = Nat.choose (p + k - 1) k := by congr 2; omega
  exact_mod_cast hchoose

theorem powerSeries_inv_pow_of_constantCoeff_ne
    (P : PowerSeries ℂ) (hP : PowerSeries.constantCoeff P ≠ 0) (n : ℕ) :
    (P ^ n)⁻¹ = P⁻¹ ^ n := by
  apply (PowerSeries.inv_eq_iff_mul_eq_one (by simpa using pow_ne_zero n hP)).2
  rw [← mul_pow, PowerSeries.inv_mul_cancel P hP, one_pow]

theorem coeff_binomialUnitPowerSeries_inv_sq
    (r k : ℕ) (hr : 1 ≤ r) :
    PowerSeries.coeff k ((binomialUnitPowerSeries r)⁻¹ ^ 2) =
      complexSignedPoleConeCoeff (2 * r) k := by
  rw [binomialUnitPowerSeries_eq_one_add_X_pow,
    powerSeries_inv_pow_of_constantCoeff_ne (1 + PowerSeries.X) (by simp)]
  rw [← pow_mul]
  rw [show r * 2 = 2 * r by omega]
  exact coeff_inv_pow_one_add_X_eq_complexSignedPoleConeCoeff (2 * r) k (by omega)

theorem eventually_factorization_ne_zero
    {f g : ℂ → ℂ} {rho : ℂ} {r : ℕ}
    (hg : AnalyticAt ℂ g rho) (hgrho : g rho ≠ 0)
    (hfactor : ∀ z, f z = (z - rho) ^ r * g z) :
    ∀ᶠ u in nhdsWithin 0 ({0}ᶜ : Set ℂ), f (rho + u) ≠ 0 := by
  have hshift : Tendsto (fun u : ℂ => rho + u) (nhdsWithin 0 ({0}ᶜ : Set ℂ))
      (nhds rho) := by
    have hc : Tendsto (fun _ : ℂ => rho) (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds rho) :=
      tendsto_const_nhds
    have hi : Tendsto (fun u : ℂ => u) (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds 0) :=
      tendsto_id.mono_left inf_le_left
    simpa using hc.add hi
  have hgne : ∀ᶠ u in nhdsWithin 0 ({0}ᶜ : Set ℂ), g (rho + u) ≠ 0 :=
    hshift.eventually (hg.continuousAt.eventually_ne hgrho)
  have hune : ∀ᶠ u in nhdsWithin 0 ({0}ᶜ : Set ℂ), u ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hu
  filter_upwards [hgne, hune] with u hgu hu
  rw [hfactor]
  exact mul_ne_zero (pow_ne_zero r (by simpa using hu)) hgu

/-- The exact zero model controls every reciprocal-square coefficient after pole rescaling. -/
theorem tendsto_scaled_causticReciprocalSquareCoeff_of_factorization
    {f g : ℂ → ℂ} {rho : ℂ} {r : ℕ}
    (hr : 1 ≤ r) (hg : AnalyticAt ℂ g rho) (hgrho : g rho ≠ 0)
    (hfactor : ∀ z, f z = (z - rho) ^ r * g z) (k : ℕ) :
    Tendsto (fun u => u ^ k * causticReciprocalSquareCoeff f (rho + u) k)
      (nhdsWithin 0 ({0}ᶜ : Set ℂ))
      (nhds (complexSignedPoleConeCoeff (2 * r) k)) := by
  let P : ℂ → PowerSeries ℂ := fun u =>
    PowerSeries.rescale u (normalizedAnalyticJetSeries f (rho + u))
  let Pgood : ℂ → PowerSeries ℂ := fun u =>
    if f (rho + u) = 0 then 1 else P u
  have hfne := eventually_factorization_ne_zero hg hgrho hfactor
  have hP0 : ∀ u, PowerSeries.constantCoeff (Pgood u) = 1 := by
    intro u
    by_cases hfu : f (rho + u) = 0
    · simp [Pgood, hfu]
    · simp only [Pgood, hfu, if_false, P]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale]
      simpa using normalizedAnalyticJetSeries_constantCoeff hfu
  have hB0 : PowerSeries.constantCoeff (binomialUnitPowerSeries r) = 1 := by
    simp [binomialUnitPowerSeries]
  have hPcoeff : ∀ j, Tendsto (fun u => PowerSeries.coeff j (Pgood u))
      (nhdsWithin 0 ({0}ᶜ : Set ℂ))
      (nhds (PowerSeries.coeff j (binomialUnitPowerSeries r))) := by
    intro j
    have hlim := tendsto_coeff_rescale_normalized_factorization hg hgrho hfactor j
    apply hlim.congr'
    filter_upwards [hfne] with u hfu
    simp only [Pgood, hfu, if_false, P]
  have hinv := tendsto_coeff_inv_sq_of_tendsto_coeff hP0 hB0 hPcoeff k
  rw [coeff_binomialUnitPowerSeries_inv_sq r k hr] at hinv
  have hinv' : Tendsto
      (fun u => PowerSeries.coeff k ((P u)⁻¹ ^ 2))
      (nhdsWithin 0 ({0}ᶜ : Set ℂ))
      (nhds (complexSignedPoleConeCoeff (2 * r) k)) := by
    apply hinv.congr'
    filter_upwards [hfne] with u hfu
    simp only [Pgood, hfu, if_false]
  apply hinv'.congr'
  filter_upwards [hfne] with u hfu
  simpa only [P] using (scaled_causticReciprocalSquareCoeff (u := u) hfu k).symm

/-- Determinant-level pole rescaling converges to the universal signed binomial Toeplitz model. -/
theorem tendsto_scaled_causticTau_of_factorization
    {f g : ℂ → ℂ} {rho : ℂ} {r : ℕ}
    (hr : 1 ≤ r) (hg : AnalyticAt ℂ g rho) (hgrho : g rho ≠ 0)
    (hfactor : ∀ z, f z = (z - rho) ^ r * g z) (n m : ℕ) :
    Tendsto (fun u => u ^ (m * n) * causticTau f n m (rho + u))
      (nhdsWithin 0 ({0}ᶜ : Set ℂ))
      (nhds (complexSignedPoleConeToeplitz (2 * r) n m).det) := by
  have hdet := tendsto_det_rectangularSchurToeplitz_of_tendsto
    (a := fun k u => u ^ k * causticReciprocalSquareCoeff f (rho + u) k)
    (c := complexSignedPoleConeCoeff (2 * r)) n m
    (fun k => tendsto_scaled_causticReciprocalSquareCoeff_of_factorization
      hr hg hgrho hfactor k)
  have hdet' : Tendsto
      (fun u => (rectangularSchurToeplitz
        (fun k => u ^ k * causticReciprocalSquareCoeff f (rho + u) k) n m).det)
      (nhdsWithin 0 ({0}ᶜ : Set ℂ))
      (nhds (complexSignedPoleConeToeplitz (2 * r) n m).det) := by
    simpa only [complexSignedPoleConeToeplitz] using hdet
  apply hdet'.congr'
  have hune : ∀ᶠ u in nhdsWithin 0 ({0}ᶜ : Set ℂ), u ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hu
  filter_upwards [hune] with u hu
  simpa only [causticTau] using rectangularSchurToeplitz_scaled_det
    (causticReciprocalSquareCoeff f (rho + u)) u n m hu

def reciprocalNormalizedJetSeries (f : ℂ → ℂ) (s : ℂ) : PowerSeries ℂ :=
  PowerSeries.C (f s) *
    GaloisForLFunctions.analyticJetPowerSeries (fun z => (f z)⁻¹) s

theorem reciprocalNormalizedJetSeries_coeff (f : ℂ → ℂ) (s : ℂ) (j : ℕ) :
    PowerSeries.coeff j (reciprocalNormalizedJetSeries f s) =
      f s * (((j.factorial : ℂ)⁻¹) * iteratedDeriv j (fun z => (f z)⁻¹) s) := by
  rw [reciprocalNormalizedJetSeries, PowerSeries.coeff_C_mul]
  simp [GaloisForLFunctions.analyticJetPowerSeries]

theorem normalizedAnalyticJetSeries_inv_eq_reciprocal
    {f : ℂ → ℂ} {s : ℂ}
    (hf : ∀ n : ℕ, ContDiffAt ℂ n f s) (hfs : f s ≠ 0) :
    (normalizedAnalyticJetSeries f s)⁻¹ = reciprocalNormalizedJetSeries f s := by
  apply (PowerSeries.inv_eq_iff_mul_eq_one (by
    rw [normalizedAnalyticJetSeries_constantCoeff hfs]
    exact one_ne_zero)).2
  rw [normalizedAnalyticJetSeries, reciprocalNormalizedJetSeries]
  have hj := GaloisForLFunctions.analyticJetPowerSeries_mul_inv hf hfs
  calc
    (PowerSeries.C (f s) *
        GaloisForLFunctions.analyticJetPowerSeries (fun z => (f z)⁻¹) s) *
        (PowerSeries.C (f s)⁻¹ * GaloisForLFunctions.analyticJetPowerSeries f s) =
      (PowerSeries.C (f s) * PowerSeries.C (f s)⁻¹) *
        (GaloisForLFunctions.analyticJetPowerSeries f s *
          GaloisForLFunctions.analyticJetPowerSeries (fun z => (f z)⁻¹) s) := by
            ac_rfl
    _ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hfs, map_one, hj, one_mul]

def causticMeromorphicCoeff (f : ℂ → ℂ) (s : ℂ) (k : ℕ) : ℂ :=
  ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) k,
    PowerSeries.coeff x.1 (reciprocalNormalizedJetSeries f s) *
      PowerSeries.coeff x.2 (reciprocalNormalizedJetSeries f s)

theorem causticReciprocalSquareCoeff_eq_meromorphicCoeff
    {f : ℂ → ℂ} {s : ℂ}
    (hf : ∀ n : ℕ, ContDiffAt ℂ n f s) (hfs : f s ≠ 0) (k : ℕ) :
    causticReciprocalSquareCoeff f s k = causticMeromorphicCoeff f s k := by
  rw [causticReciprocalSquareCoeff, normalizedAnalyticJetSeries_inv_eq_reciprocal hf hfs,
    pow_two, PowerSeries.coeff_mul]
  rfl

theorem meromorphicAt_finset_sum_family
    {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (rho : ℂ)
    (hF : ∀ i ∈ s, MeromorphicAt (F i) rho) :
    MeromorphicAt (fun z => ∑ i ∈ s, F i z) rho := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hF a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

theorem meromorphicAt_reciprocalNormalizedJetSeries_coeff
    {f : ℂ → ℂ} {rho : ℂ} (hf : AnalyticAt ℂ f rho) (j : ℕ) :
    MeromorphicAt (fun s => PowerSeries.coeff j (reciprocalNormalizedJetSeries f s)) rho := by
  have hfinv : MeromorphicAt (fun s => (f s)⁻¹) rho := hf.meromorphicAt.inv
  have hjet := meromorphicAt_iteratedDeriv hfinv j
  have hconst : MeromorphicAt (fun _ : ℂ => ((j.factorial : ℂ)⁻¹)) rho :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => ((j.factorial : ℂ)⁻¹)) rho).meromorphicAt
  rw [show (fun s => PowerSeries.coeff j (reciprocalNormalizedJetSeries f s)) =
      f * ((fun _ : ℂ => ((j.factorial : ℂ)⁻¹)) *
        iteratedDeriv j (fun s => (f s)⁻¹)) by
    funext s
    simp only [Pi.mul_apply, reciprocalNormalizedJetSeries_coeff]]
  exact hf.meromorphicAt.mul (hconst.mul hjet)

theorem meromorphicAt_causticMeromorphicCoeff
    {f : ℂ → ℂ} {rho : ℂ} (hf : AnalyticAt ℂ f rho) (k : ℕ) :
    MeromorphicAt (fun s => causticMeromorphicCoeff f s k) rho := by
  apply meromorphicAt_finset_sum_family
  intro x hx
  exact (meromorphicAt_reciprocalNormalizedJetSeries_coeff hf x.1).mul
    (meromorphicAt_reciprocalNormalizedJetSeries_coeff hf x.2)

theorem eventually_factorization_ne_zero_at
    {f g : ℂ → ℂ} {rho : ℂ} {r : ℕ}
    (hg : AnalyticAt ℂ g rho) (hgrho : g rho ≠ 0)
    (hfactor : ∀ z, f z = (z - rho) ^ r * g z) :
    ∀ᶠ s in nhdsWithin rho ({rho}ᶜ : Set ℂ), f s ≠ 0 := by
  have hgne : ∀ᶠ s in nhdsWithin rho ({rho}ᶜ : Set ℂ), g s ≠ 0 :=
    (hg.continuousAt.eventually_ne hgrho).filter_mono inf_le_left
  have hsne : ∀ᶠ s in nhdsWithin rho ({rho}ᶜ : Set ℂ), s ≠ rho := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
  filter_upwards [hgne, hsne] with s hgs hs
  rw [hfactor]
  exact mul_ne_zero (pow_ne_zero r (sub_ne_zero.mpr hs)) hgs

theorem meromorphicAt_causticReciprocalSquareCoeff_of_factorization
    {f g : ℂ → ℂ} {rho : ℂ} {r : ℕ}
    (hf : AnalyticAt ℂ f rho) (hg : AnalyticAt ℂ g rho) (hgrho : g rho ≠ 0)
    (hfactor : ∀ z, f z = (z - rho) ^ r * g z) (k : ℕ) :
    MeromorphicAt (fun s => causticReciprocalSquareCoeff f s k) rho := by
  apply (meromorphicAt_causticMeromorphicCoeff hf k).congr
  have hfan : ∀ᶠ s in nhdsWithin rho ({rho}ᶜ : Set ℂ), AnalyticAt ℂ f s :=
    hf.eventually_analyticAt.filter_mono inf_le_left
  filter_upwards [hfan, eventually_factorization_ne_zero_at hg hgrho hfactor] with s hfs hne
  exact (causticReciprocalSquareCoeff_eq_meromorphicCoeff
    (fun n => hfs.contDiffAt) hne k).symm

theorem meromorphicAt_finset_prod_family
    {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (rho : ℂ)
    (hF : ∀ i ∈ s, MeromorphicAt (F i) rho) :
    MeromorphicAt (fun z => ∏ i ∈ s, F i z) rho := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hF a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

theorem meromorphicAt_matrix_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℂ → Matrix ι ι ℂ) (rho : ℂ)
    (hA : ∀ i j, MeromorphicAt (fun z => A z i j) rho) :
    MeromorphicAt (fun z => (A z).det) rho := by
  let D : ℂ → ℂ := fun z =>
    ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ∏ i, A z (σ i) i
  have hD : (fun z => (A z).det) = D := by
    funext z
    rw [Matrix.det_apply']
  rw [hD]
  apply meromorphicAt_finset_sum_family Finset.univ
  intro σ hσ
  have hc : MeromorphicAt
      (fun _ : ℂ => (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) rho :=
    (analyticAt_const : AnalyticAt ℂ
      (fun _ : ℂ => (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) rho).meromorphicAt
  have hp : MeromorphicAt (fun z => ∏ i, A z (σ i) i) rho := by
    simpa using meromorphicAt_finset_prod_family Finset.univ
      (fun i z => A z (σ i) i) rho (fun i hi => hA (σ i) i)
  rw [show (fun z => (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
      ∏ i, A z (σ i) i) =
      (fun _ : ℂ => (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) *
        (fun z => ∏ i, A z (σ i) i) by rfl]
  exact hc.mul hp

theorem meromorphicAt_causticTau_of_factorization
    {f g : ℂ → ℂ} {rho : ℂ} {r : ℕ}
    (hf : AnalyticAt ℂ f rho) (hg : AnalyticAt ℂ g rho) (hgrho : g rho ≠ 0)
    (hfactor : ∀ z, f z = (z - rho) ^ r * g z) (n m : ℕ) :
    MeromorphicAt (fun s => causticTau f n m s) rho := by
  rw [show (fun s => causticTau f n m s) = fun s =>
      (rectangularSchurToeplitz (causticReciprocalSquareCoeff f s) n m).det by rfl]
  apply meromorphicAt_matrix_det
  intro i j
  by_cases hij : (j : ℕ) ≤ n + (i : ℕ)
  · simpa only [rectangularSchurToeplitz, hij, if_pos] using
      meromorphicAt_causticReciprocalSquareCoeff_of_factorization
        hf hg hgrho hfactor (n + (i : ℕ) - (j : ℕ))
  · have hzero : MeromorphicAt (fun _ : ℂ => (0 : ℂ)) rho :=
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) rho).meromorphicAt
    simpa only [rectangularSchurToeplitz, hij, if_false] using hzero

theorem tendsto_sub_const_punctured (rho : ℂ) :
    Tendsto (fun z : ℂ => z - rho) (nhdsWithin rho ({rho}ᶜ : Set ℂ))
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) := by
  let l := nhdsWithin rho ({rho}ᶜ : Set ℂ)
  have hnhds : Tendsto (fun z : ℂ => z - rho) l (nhds 0) := by
    have hid : Tendsto (fun z : ℂ => z) l (nhds rho) :=
      tendsto_id.mono_left inf_le_left
    simpa [l] using hid.sub_const rho
  have hprincipal : Tendsto (fun z : ℂ => z - rho) l
      (Filter.principal ({0}ᶜ : Set ℂ)) := by
    apply Filter.tendsto_principal.2
    filter_upwards [self_mem_nhdsWithin] with z hz
    change z ≠ rho at hz
    exact Set.mem_compl (sub_ne_zero.mpr hz)
  have h := hnhds.inf hprincipal
  simpa only [l, nhdsWithin, inf_idem] using h

theorem tendsto_scaled_causticTau_at_of_factorization
    {f g : ℂ → ℂ} {rho : ℂ} {r : ℕ}
    (hr : 1 ≤ r) (hg : AnalyticAt ℂ g rho) (hgrho : g rho ≠ 0)
    (hfactor : ∀ z, f z = (z - rho) ^ r * g z) (n m : ℕ) :
    Tendsto (fun z => (z - rho) ^ (m * n) * causticTau f n m z)
      (nhdsWithin rho ({rho}ᶜ : Set ℂ))
      (nhds (complexSignedPoleConeToeplitz (2 * r) n m).det) := by
  have h := (tendsto_scaled_causticTau_of_factorization
    hr hg hgrho hfactor n m).comp (tendsto_sub_const_punctured rho)
  have hfun :
      (fun z => (z - rho) ^ (m * n) * causticTau f n m z) =
        (fun u => u ^ (m * n) * causticTau f n m (rho + u)) ∘
          (fun z => z - rho) := by
    funext z
    simp only [Function.comp_apply]
    congr 2
    ring
  rw [hfun]
  exact h

/-- Exact pole-cone cutoff: rank `m` has full pole order exactly through `m = 2r`. -/
theorem causticTau_meromorphicOrderAt_eq_neg_iff
    {f : ℂ → ℂ} {rho : ℂ} {r n m : ℕ}
    (hf : AnalyticAt ℂ f rho) (hr : 1 ≤ r)
    (horder : analyticOrderAt f rho = r) (hn : 1 ≤ n) :
    meromorphicOrderAt (fun s => causticTau f n m s) rho =
        ((-(m * n : ℤ) : ℤ) : WithTop ℤ) ↔
      m ≤ 2 * r := by
  obtain ⟨g, hg, hgrho, hfactor⟩ :=
    exists_global_factor_of_analyticOrderAt_eq_natCast hf hr horder
  have hmero := meromorphicAt_causticTau_of_factorization hf hg hgrho hfactor n m
  have hlim := tendsto_scaled_causticTau_at_of_factorization
    hr hg hgrho hfactor n m
  constructor
  · intro heq
    by_contra hm
    have hdetzero : (complexSignedPoleConeToeplitz (2 * r) n m).det = 0 := by
      apply not_ne_iff.mp
      intro hne
      have hcut := (complexSignedPoleConeToeplitz_det_ne_zero_iff
        (2 * r) n m (by omega) hn).1 hne
      omega
    have hlim0 : Tendsto
        (fun z => (z - rho) ^ (m * n) * causticTau f n m z)
        (nhdsWithin rho ({rho}ᶜ : Set ℂ)) (nhds 0) := by
      simpa only [hdetzero] using hlim
    have hstrict := neg_nat_lt_meromorphicOrderAt_of_tendsto_pow_mul_zero
      (m * n) hmero hlim0
    rw [heq] at hstrict
    exact (lt_irrefl _ hstrict)
  · intro hm
    have hdetne : (complexSignedPoleConeToeplitz (2 * r) n m).det ≠ 0 :=
      (complexSignedPoleConeToeplitz_det_ne_zero_iff
        (2 * r) n m (by omega) hn).2 hm
    exact meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul
      (m * n) hmero hdetne hlim

/-- The zero multiplicity is recovered as half the greatest full-pole Toeplitz rank. -/
theorem causticTau_fullPoleRanks_isGreatest
    {f : ℂ → ℂ} {rho : ℂ} {r n : ℕ}
    (hf : AnalyticAt ℂ f rho) (hr : 1 ≤ r)
    (horder : analyticOrderAt f rho = r) (hn : 1 ≤ n) :
    IsGreatest
      {m : ℕ | 1 ≤ m ∧
        meromorphicOrderAt (fun s => causticTau f n m s) rho =
          ((-(m * n : ℤ) : ℤ) : WithTop ℤ)}
      (2 * r) := by
  constructor
  · constructor
    · omega
    · exact (causticTau_meromorphicOrderAt_eq_neg_iff hf hr horder hn).2 le_rfl
  · intro m hm
    exact (causticTau_meromorphicOrderAt_eq_neg_iff hf hr horder hn).1 hm.2

/-- Beyond the cone width, cancellation strictly improves the naive pole order. -/
theorem causticTau_meromorphicOrderAt_gt_neg
    {f : ℂ → ℂ} {rho : ℂ} {r n m : ℕ}
    (hf : AnalyticAt ℂ f rho) (hr : 1 ≤ r)
    (horder : analyticOrderAt f rho = r) (hn : 1 ≤ n)
    (hm : 2 * r < m) :
    ((-(m * n : ℤ) : ℤ) : WithTop ℤ) <
      meromorphicOrderAt (fun s => causticTau f n m s) rho := by
  obtain ⟨g, hg, hgrho, hfactor⟩ :=
    exists_global_factor_of_analyticOrderAt_eq_natCast hf hr horder
  have hmero := meromorphicAt_causticTau_of_factorization hf hg hgrho hfactor n m
  have hlim := tendsto_scaled_causticTau_at_of_factorization
    hr hg hgrho hfactor n m
  have hdetzero : (complexSignedPoleConeToeplitz (2 * r) n m).det = 0 := by
    apply not_ne_iff.mp
    intro hne
    have hcut := (complexSignedPoleConeToeplitz_det_ne_zero_iff
      (2 * r) n m (by omega) hn).1 hne
    omega
  have hlim0 : Tendsto
      (fun z => (z - rho) ^ (m * n) * causticTau f n m z)
      (nhdsWithin rho ({rho}ᶜ : Set ℂ)) (nhds 0) := by
    simpa only [hdetzero] using hlim
  exact neg_nat_lt_meromorphicOrderAt_of_tendsto_pow_mul_zero
    (m * n) hmero hlim0

/-- Depth zero is the unit boundary of every local caustic tower. -/
theorem causticTau_meromorphicOrderAt_zero_depth
    {f : ℂ → ℂ} {rho : ℂ} {r m : ℕ}
    (hf : AnalyticAt ℂ f rho) (hr : 1 ≤ r)
    (horder : analyticOrderAt f rho = r) :
    meromorphicOrderAt (fun s => causticTau f 0 m s) rho = 0 := by
  obtain ⟨g, hg, hgrho, hfactor⟩ :=
    exists_global_factor_of_analyticOrderAt_eq_natCast hf hr horder
  have hmero := meromorphicAt_causticTau_of_factorization hf hg hgrho hfactor 0 m
  have hlim := tendsto_scaled_causticTau_at_of_factorization
    hr hg hgrho hfactor 0 m
  have hcoeffzero : complexSignedPoleConeCoeff (2 * r) 0 = 1 := by
    simp [complexSignedPoleConeCoeff]
  have hdet : (complexSignedPoleConeToeplitz (2 * r) 0 m).det = 1 := by
    simpa only [complexSignedPoleConeToeplitz, horizonAmplitude] using
      horizonAmplitude_zero_depth
        (complexSignedPoleConeCoeff (2 * r)) m hcoeffzero
  have hlim' : Tendsto
      (fun z => (z - rho) ^ (m * 0) * causticTau f 0 m z)
      (nhdsWithin rho ({rho}ᶜ : Set ℂ)) (nhds 1) := by
    simpa only [hdet] using hlim
  simpa using meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul
    0 hmero one_ne_zero hlim'

/-- Every depth, including the unit boundary at depth zero, has the expected order inside the
finite pole cone. -/
theorem causticTau_meromorphicOrderAt_eq_neg_of_rank_le
    {f : ℂ → ℂ} {rho : ℂ} {r n m : ℕ}
    (hf : AnalyticAt ℂ f rho) (hr : 1 ≤ r)
    (horder : analyticOrderAt f rho = r) (hm : m ≤ 2 * r) :
    meromorphicOrderAt (fun s => causticTau f n m s) rho =
      ((-(m * n : ℤ) : ℤ) : WithTop ℤ) := by
  obtain _ | n := n
  · simpa using causticTau_meromorphicOrderAt_zero_depth
      (m := m) hf hr horder
  · exact (causticTau_meromorphicOrderAt_eq_neg_iff
      hf hr horder (by omega)).2 hm

/-- The analytic caustic tower satisfies the all-rank static Q-system with no pivot hypothesis. -/
theorem causticTau_qSystem (f : ℂ → ℂ) (s : ℂ)
    (c n : ℕ) (hn : 0 < n) :
    causticTau f n (c + 1) s ^ 2 =
      causticTau f (n - 1) (c + 1) s *
          causticTau f (n + 1) (c + 1) s +
        causticTau f n c s * causticTau f n (c + 2) s := by
  simpa only [causticTau, horizonAmplitude] using
    horizonAmplitude_qSystem (causticReciprocalSquareCoeff f s) c n hn

/-- At rank `2r`, the horizontal tropical Q-system candidate equals twice the central order,
whereas the vertical candidate is strictly larger.  Thus the minimum is uniquely horizontal. -/
theorem causticTau_tropical_boundary_unique_horizontal
    {f : ℂ → ℂ} {rho : ℂ} {r n : ℕ}
    (hf : AnalyticAt ℂ f rho) (hr : 1 ≤ r)
    (horder : analyticOrderAt f rho = r) (hn : 1 ≤ n) :
    let horizontal :=
      meromorphicOrderAt (fun s => causticTau f (n - 1) (2 * r) s) rho +
        meromorphicOrderAt (fun s => causticTau f (n + 1) (2 * r) s) rho
    let vertical :=
      meromorphicOrderAt (fun s => causticTau f n (2 * r - 1) s) rho +
        meromorphicOrderAt (fun s => causticTau f n (2 * r + 1) s) rho
    let centerTwice :=
      meromorphicOrderAt (fun s => causticTau f n (2 * r) s) rho +
        meromorphicOrderAt (fun s => causticTau f n (2 * r) s) rho
    centerTwice = horizontal ∧ horizontal < vertical ∧
      min horizontal vertical = horizontal := by
  dsimp only
  have hcenter := causticTau_meromorphicOrderAt_eq_neg_of_rank_le
    (n := n) (m := 2 * r) hf hr horder le_rfl
  have hleft := causticTau_meromorphicOrderAt_eq_neg_of_rank_le
    (n := n - 1) (m := 2 * r) hf hr horder le_rfl
  have hright := causticTau_meromorphicOrderAt_eq_neg_of_rank_le
    (n := n + 1) (m := 2 * r) hf hr horder le_rfl
  have hminus := causticTau_meromorphicOrderAt_eq_neg_of_rank_le
    (n := n) (m := 2 * r - 1) hf hr horder (by omega)
  have hplus := causticTau_meromorphicOrderAt_gt_neg
    (n := n) (m := 2 * r + 1) hf hr horder hn (by omega)
  rw [hcenter, hleft, hright, hminus]
  constructor
  · rw [← WithTop.coe_add, ← WithTop.coe_add]
    rw [WithTop.coe_eq_coe]
    norm_num [Nat.cast_sub hn]
    ring
  · have hvertical :
        ((-(((2 * r) * (n - 1) : ℕ) : ℤ) : ℤ) : WithTop ℤ) +
            ((-(((2 * r) * (n + 1) : ℕ) : ℤ) : ℤ) : WithTop ℤ) <
          ((-(((2 * r - 1) * n : ℕ) : ℤ) : ℤ) : WithTop ℤ) +
            meromorphicOrderAt (fun s => causticTau f n (2 * r + 1) s) rho := by
      let a : ℤ := -(((2 * r - 1) * n : ℕ) : ℤ)
      have hadd := (WithTop.add_lt_add_iff_left
        (x := (a : WithTop ℤ)) WithTop.coe_ne_top).2 hplus
      dsimp only [a] at hadd
      have hsum :
          ((-(((2 * r) * (n - 1) : ℕ) : ℤ) : ℤ) : WithTop ℤ) +
              ((-(((2 * r) * (n + 1) : ℕ) : ℤ) : ℤ) : WithTop ℤ) =
            ((-(((2 * r - 1) * n : ℕ) : ℤ) : ℤ) : WithTop ℤ) +
              ((-(((2 * r + 1) * n : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
        rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_eq_coe]
        norm_num [Nat.cast_sub hn, Nat.cast_sub (show 1 ≤ 2 * r by omega)]
        ring
      rw [hsum]
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hadd
    exact ⟨hvertical, min_eq_left hvertical.le⟩

/-- Reflection transports the Taylor jet by the sign rescaling `t ↦ -t`. -/
theorem analyticJetPowerSeries_reflection
    {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f (1 - s))
    (hreflect : ∀ z, f z = f (1 - z)) :
    GaloisForLFunctions.analyticJetPowerSeries f (1 - s) =
      PowerSeries.rescale (-1) (GaloisForLFunctions.analyticJetPowerSeries f s) := by
  apply PowerSeries.ext
  intro k
  rw [PowerSeries.coeff_rescale]
  simp only [GaloisForLFunctions.analyticJetPowerSeries, PowerSeries.coeff_mk]
  have hfun : (fun w => f (1 - w)) = f := by
    funext w
    exact (hreflect w).symm
  have hchain := iteratedDeriv_comp_one_sub_of_analyticAt k hf
  rw [hfun] at hchain
  have hderiv :
      iteratedDeriv k f (1 - s) =
        (-1 : ℂ) ^ k * iteratedDeriv k f s := by
    symm
    calc
      (-1 : ℂ) ^ k * iteratedDeriv k f s =
          (-1 : ℂ) ^ k *
            ((-1 : ℂ) ^ k * iteratedDeriv k f (1 - s)) := by rw [hchain]
      _ = iteratedDeriv k f (1 - s) := by
        rw [← mul_assoc, ← pow_add]
        simp
  rw [hderiv]
  ring

/-- The value-normalized Taylor jet obeys the same reflection rescaling. -/
theorem normalizedAnalyticJetSeries_reflection
    {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f (1 - s))
    (hreflect : ∀ z, f z = f (1 - z)) :
    normalizedAnalyticJetSeries f (1 - s) =
      PowerSeries.rescale (-1) (normalizedAnalyticJetSeries f s) := by
  rw [normalizedAnalyticJetSeries, normalizedAnalyticJetSeries,
    analyticJetPowerSeries_reflection hf hreflect]
  have hvalue : f (1 - s) = f s := (hreflect s).symm
  rw [hvalue]
  rw [map_mul]
  congr 1
  apply PowerSeries.ext
  intro k
  rw [PowerSeries.coeff_rescale]
  obtain _ | k := k
  · simp
  · simp

/-- Reciprocal-square coefficients inherit coefficient parity from source reflection. -/
theorem causticReciprocalSquareCoeff_reflection
    {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f (1 - s))
    (hreflect : ∀ z, f z = f (1 - z)) (hfs : f s ≠ 0) (k : ℕ) :
    causticReciprocalSquareCoeff f (1 - s) k =
      (-1 : ℂ) ^ k * causticReciprocalSquareCoeff f s k := by
  have hP : PowerSeries.constantCoeff (normalizedAnalyticJetSeries f s) ≠ 0 := by
    rw [normalizedAnalyticJetSeries_constantCoeff hfs]
    exact one_ne_zero
  rw [causticReciprocalSquareCoeff, causticReciprocalSquareCoeff,
    normalizedAnalyticJetSeries_reflection hf hreflect]
  rw [← PowerSeries.rescale_inv (-1) (normalizedAnalyticJetSeries f s) hP]
  rw [← map_pow]
  exact PowerSeries.coeff_rescale _ _ _

/-- Exact reflection parity of every analytic caustic away from the source divisor. -/
theorem causticTau_reflection
    {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f (1 - s))
    (hreflect : ∀ z, f z = f (1 - z)) (hfs : f s ≠ 0) (n m : ℕ) :
    causticTau f n m (1 - s) =
      (-1 : ℂ) ^ (m * n) * causticTau f n m s := by
  have hcoeff : causticReciprocalSquareCoeff f (1 - s) =
      fun k => (-1 : ℂ) ^ k * causticReciprocalSquareCoeff f s k := by
    funext k
    exact causticReciprocalSquareCoeff_reflection hf hreflect hfs k
  rw [causticTau, causticTau, hcoeff]
  exact rectangularSchurToeplitz_det_reflection
    (causticReciprocalSquareCoeff f s) n m

/-- Odd-area caustics vanish at the reflection-fixed point `1/2`. -/
theorem causticTau_half_eq_zero_of_odd
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f (1 / 2))
    (hreflect : ∀ z, f z = f (1 - z)) (hfhalf : f (1 / 2) ≠ 0)
    {n m : ℕ} (hodd : Odd (m * n)) :
    causticTau f n m (1 / 2) = 0 := by
  have hf' : AnalyticAt ℂ f ((1 : ℂ) - 1 / 2) := by
    rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]
    exact hf
  have hparity := causticTau_reflection
    (s := (1 / 2 : ℂ)) hf' hreflect hfhalf n m
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, hodd.neg_one_pow] at hparity
  have htwo : (2 : ℂ) * causticTau f n m (1 / 2) = 0 := by
    linear_combination hparity
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end

end GaloisForLFunctions.HTGeometry
