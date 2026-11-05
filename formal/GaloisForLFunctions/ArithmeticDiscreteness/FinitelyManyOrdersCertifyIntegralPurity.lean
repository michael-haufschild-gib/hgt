import GaloisForLFunctions.ArithmeticDiscreteness.ImpurityIsQuantized
import GaloisForLFunctions.HTGeometry.PowerSumTuranLowerBound

/-!
# Finitely many orders certify integral purity

In the function-field model the camera records the eigenvalue power sums
`S_ν = Σ_α α^ν = q^ν + 1 − N_ν`. For real configurations a size bound at finitely many orders is
never a certificate (`not_certified_at_finitely_many_orders`): a trace point `r + 1/r`, `r > 1`
close to `1`, is impure while `r^ν + r^{−ν} ≤ 3` for all `ν ≤ M`. Integrality changes this.

* **Eigenvalue bounds give near purity** (`trace_near_of_eigen_bound`). If `α` and `q/α` both have
  modulus `≤ √q(1+κ)`, the trace point `τ = α + q/α` has `|Im τ| ≤ 2√q κ` and
  `|Re τ| ≤ √q(2 + κ²)`.
* **Integral configurations have a definite top eigenvalue** (`exists_large_eigenvalue`). If some
  trace point of a monic `h ∈ ℤ[X]` is impure, some eigenvalue has modulus `> √q(1+κ)`, for every
  `κ ∈ (0,1]` below the quantization scale of `ImpurityIsQuantized`.
* **The finite certificate** (`isPureTrace_of_bounded_powerSums`). If `|S_ν| ≤ B q^{ν/2}` at the
  `N` consecutive orders `M+1, …, M+N` (`N` the number of eigenvalues) and
  `B · L_N(M) < (1+κ)^{M+1}`, `L_N(M)` the constant of Turán's second main theorem
  (`HTGeometry.exists_norm_powerSum_ge_scaled`), then every trace point is pure.
* **Depth gap** (`exists_deep_eigenvalue_of_not_pure`). An impure integral configuration has a
  zero of its zeta function at depth `Re s − ½ > log(1+κ)/log q`.
* **Eventually certified** (`eventually_isPureTrace_of_bounded_powerSums`). For fixed degree, disc
  and `B`, the bound at `N` consecutive orders past some `M₀` certifies purity.

Discreteness is the amplifier: it turns the all-orders certificate
(`ZeroConfigurationGeometry.isPure_iff_bounded_curveImage`) into a finite one, by quantizing the
top eigenvalue away from the circle so that Turán's lower bound outgrows any fixed size bound.
-/

open Polynomial Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- The imaginary quantization scale `(2R)^{−((n−1)²+n−2)}`. -/
def gapIm (R : ℝ) (n : ℕ) : ℝ := ((2 * R) ^ ((n - 1) ^ 2 + (n - 2)))⁻¹

/-- The edge quantization scale `((R + 2√q)(R² + 4q)^{n−1})⁻¹`. -/
def gapEdge (q : ℕ) (R : ℝ) (n : ℕ) : ℝ := ((R + 2 * Real.sqrt q) * (R ^ 2 + 4 * q) ^ (n - 1))⁻¹

/-- The constant `2e N (6(N+1)(M+2N+2))^N` of Turán's second main theorem. -/
def turanConst (N M : ℕ) : ℝ := 2 * (Real.exp 1 * N * (6 * (N + 1) * ((M : ℝ) + 2 * N + 2)) ^ N)

theorem turanConst_pos {N : ℕ} (hN : 1 ≤ N) (M : ℕ) : 0 < turanConst N M := by
  unfold turanConst
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

/-- **Eigenvalue bounds give near purity.** If `z ≠ 0` and both `z` and `q/z` have modulus at most
`√q(1+κ)`, then `τ = z + q/z` has `|Im τ| ≤ 2√q κ` and `|Re τ| ≤ √q(2 + κ²)`. -/
theorem trace_near_of_eigen_bound {q : ℝ} (hq : 0 < q) {κ : ℝ} (hκ : 0 ≤ κ) {z : ℂ}
    (hz : z ≠ 0) (h1 : ‖z‖ ≤ Real.sqrt q * (1 + κ)) (h2 : ‖(q : ℂ) / z‖ ≤ Real.sqrt q * (1 + κ)) :
    |(z + q / z).im| ≤ 2 * Real.sqrt q * κ ∧ |(z + q / z).re| ≤ Real.sqrt q * (2 + κ ^ 2) := by
  set a := ‖z‖ with ha
  set s := Real.sqrt q with hs
  have ha0 : 0 < a := norm_pos_iff.mpr hz
  have hs0 : 0 < s := Real.sqrt_pos.mpr hq
  have hss : s * s = q := Real.mul_self_sqrt hq.le
  have hnsq : normSq z = a ^ 2 := by rw [normSq_eq_norm_sq]
  have hqa : q / a ≤ s * (1 + κ) := by
    rwa [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] at h2
  have hc : 0 < 1 + κ := by linarith
  -- `a` lies in `[s/(1+κ), s(1+κ)]`
  have hlow : s ≤ a * (1 + κ) := by
    rw [div_le_iff₀ ha0] at hqa
    nlinarith
  have him : (z + q / z).im = z.im * (1 - q / a ^ 2) := by
    rw [add_im, div_im, hnsq]; simp; ring
  have hre : (z + q / z).re = z.re * (1 + q / a ^ 2) := by
    rw [add_re, div_re, hnsq]; simp; ring
  have hzi : |z.im| ≤ a := abs_im_le_norm z
  have hzr : |z.re| ≤ a := abs_re_le_norm z
  constructor
  · rw [him, abs_mul]
    have hkey : a * |1 - q / a ^ 2| ≤ 2 * s * κ := by
      have heq : a * |1 - q / a ^ 2| = |a - q / a| := by
        rw [← abs_of_pos ha0, ← abs_mul, abs_of_pos ha0]; congr 1; field_simp
      rw [heq, abs_le]
      have hqa' : q / a = s * s / a := by rw [hss]
      constructor
      · -- `q/a − a ≤ 2sκ`
        have : q / a - a ≤ s * (1 + κ) - s / (1 + κ) := by
          have : s / (1 + κ) ≤ a := by rw [div_le_iff₀ hc]; linarith
          linarith
        have hk : s * (1 + κ) - s / (1 + κ) ≤ 2 * s * κ := by
          have : s * (1 + κ) - 2 * s * κ ≤ s / (1 + κ) := by
            rw [le_div_iff₀ hc]; nlinarith [mul_nonneg hs0.le (mul_nonneg hκ hκ)]
          linarith
        linarith
      · -- `a − q/a ≤ 2sκ`
        have hqa2 : s / (1 + κ) ≤ q / a := by
          rw [div_le_div_iff₀ hc ha0, ← hss]
          nlinarith
        have hk : s * (1 + κ) - s / (1 + κ) ≤ 2 * s * κ := by
          have : s * (1 + κ) - 2 * s * κ ≤ s / (1 + κ) := by
            rw [le_div_iff₀ hc]; nlinarith [mul_nonneg hs0.le (mul_nonneg hκ hκ)]
          linarith
        linarith
    calc |z.im| * |1 - q / a ^ 2| ≤ a * |1 - q / a ^ 2| :=
          mul_le_mul_of_nonneg_right hzi (abs_nonneg _)
      _ ≤ 2 * s * κ := hkey
  · rw [hre, abs_mul, abs_of_pos (by positivity : 0 < 1 + q / a ^ 2)]
    have hsum : a * (1 + q / a ^ 2) = a + q / a := by field_simp
    -- `a + q/a ≤ s(1+κ) + s/(1+κ) ≤ s(2 + κ²)`
    have hbetween : (a - s * (1 + κ)) * (a * (1 + κ) - s) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have hconv : a + q / a ≤ s * (2 + κ ^ 2) := by
      rw [← hss]
      have : a + s * s / a = (a * a + s * s) / a := by field_simp
      rw [this, div_le_iff₀ ha0]
      nlinarith [mul_nonneg hκ (mul_nonneg hκ hκ), mul_nonneg hs0.le (mul_nonneg hκ hκ),
        mul_nonneg ha0.le (mul_nonneg hκ (mul_nonneg hκ hκ))]
    calc |z.re| * (1 + q / a ^ 2) ≤ a * (1 + q / a ^ 2) :=
          mul_le_mul_of_nonneg_right hzr (by positivity)
      _ = a + q / a := hsum
      _ ≤ s * (2 + κ ^ 2) := hconv

/-- An **eigenvalue configuration** of a trace polynomial `h`: nonzero eigenvalues closed under
`α ↦ q/α`, with every trace point of `h` of the form `α + q/α`. -/
structure IsEigenConfig {ι : Type*} (q : ℕ) (h : ℤ[X]) (s : Finset ι) (z : ι → ℂ) : Prop where
  ne_zero : ∀ i ∈ s, z i ≠ 0
  pair : ∀ i ∈ s, ∃ j ∈ s, z j = (q : ℂ) / z i
  cover : ∀ τ ∈ (toC h).roots, ∃ i ∈ s, z i + (q : ℂ) / z i = τ

/-- **Integral configurations have a definite top eigenvalue.** If every eigenvalue has modulus
at most `√q(1+κ)`, where `κ ∈ [0,1]` satisfies `4√q κ < gapIm R n` and `√q κ < gapEdge q R n`,
then every trace point of the monic integer polynomial `h` is pure. -/
theorem isPureTrace_of_eigen_bound {ι : Type*} {h : ℤ[X]} (hh : h.Monic) {q : ℕ} (hq : 1 ≤ q)
    {R : ℝ} (hR1 : 1 ≤ 2 * R) (hR : ∀ z ∈ (toC h).roots, ‖z‖ ≤ R) {s : Finset ι} {z : ι → ℂ}
    (hE : IsEigenConfig q h s z) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hκim : 4 * Real.sqrt q * κ < gapIm R h.natDegree)
    (hκedge : Real.sqrt q * κ < gapEdge q R h.natDegree)
    (hbound : ∀ i ∈ s, ‖z i‖ ≤ Real.sqrt q * (1 + κ)) :
    ∀ τ ∈ (toC h).roots, IsPureTrace q τ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  refine isPureTrace_of_near hh hq hR1 hR fun τ hτ => ?_
  obtain ⟨i, hi, rfl⟩ := hE.cover τ hτ
  obtain ⟨j, hj, hzj⟩ := hE.pair i hi
  have h2 : ‖(q : ℂ) / z i‖ ≤ Real.sqrt q * (1 + κ) := by rw [← hzj]; exact hbound j hj
  have hqc : ((q : ℝ) : ℂ) = (q : ℂ) := by norm_cast
  obtain ⟨him, hre⟩ := trace_near_of_eigen_bound hq0 hκ0 (hE.ne_zero i hi) (hbound i hi)
    (by rw [hqc]; exact h2)
  rw [hqc] at him hre
  refine ⟨?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left him (by norm_num : (0 : ℝ) ≤ 2)
    unfold gapIm at hκim; linarith
  · have hsq : Real.sqrt q * κ ^ 2 ≤ Real.sqrt q * κ :=
      mul_le_mul_of_nonneg_left (by nlinarith) (Real.sqrt_nonneg _)
    unfold gapEdge at hκedge; linarith

/-- **The finite certificate.** Let `h ∈ ℤ[X]` be monic with roots in `|z| ≤ R` (`2R ≥ 1`),
`q ≥ 1`, and `z` an eigenvalue configuration of `N` eigenvalues. Let `κ ∈ (0,1]` satisfy
`4√q κ < gapIm R n` and `√q κ < gapEdge q R n`. If `|S_ν| ≤ B q^{ν/2}` for the `N` orders
`M+1 ≤ ν ≤ M+N` and `B · L_N(M) < (1+κ)^{M+1}`, every trace point of `h` is pure. -/
theorem isPureTrace_of_bounded_powerSums {ι : Type*} {h : ℤ[X]} (hh : h.Monic) {q : ℕ}
    (hq : 1 ≤ q) {R : ℝ} (hR1 : 1 ≤ 2 * R) (hR : ∀ z ∈ (toC h).roots, ‖z‖ ≤ R) {s : Finset ι}
    {z : ι → ℂ} (hE : IsEigenConfig q h s z) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hκim : 4 * Real.sqrt q * κ < gapIm R h.natDegree)
    (hκedge : Real.sqrt q * κ < gapEdge q R h.natDegree) {B : ℝ} {M : ℕ}
    (hS : ∀ ν, M + 1 ≤ ν → ν ≤ M + s.card → ‖∑ i ∈ s, z i ^ ν‖ ≤ B * Real.sqrt q ^ ν)
    (hM : B * turanConst s.card M < (1 + κ) ^ (M + 1)) :
    ∀ τ ∈ (toC h).roots, IsPureTrace q τ := by
  by_contra hnot
  have hbig : ∃ i ∈ s, Real.sqrt q * (1 + κ) ≤ ‖z i‖ := by
    by_contra hsmall
    push Not at hsmall
    exact hnot (isPureTrace_of_eigen_bound hh hq hR1 hR hE hκ0.le hκ1 hκim hκedge
      fun i hi => (hsmall i hi).le)
  have hq0 : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr (by exact_mod_cast hq)
  have hZ : 0 < Real.sqrt q * (1 + κ) := mul_pos hq0 (by linarith)
  obtain ⟨ν, hν1, hν2, hlow⟩ := HTGeometry.exists_norm_powerSum_ge_scaled s z hZ hbig M
  have hN : 1 ≤ s.card := by
    obtain ⟨i, hi, -⟩ := hbig; exact Finset.card_pos.mpr ⟨i, hi⟩
  have hL := turanConst_pos hN M
  have hup := hS ν hν1 hν2
  rw [mul_pow] at hlow
  -- `q^{ν/2}(1+κ)^ν / L ≤ |S_ν| ≤ B q^{ν/2}`
  have h1 : (1 + κ) ^ ν ≤ B * turanConst s.card M := by
    have hqν : 0 < Real.sqrt q ^ ν := pow_pos hq0 ν
    have := hlow.trans hup
    unfold turanConst
    rw [div_le_iff₀ (by unfold turanConst at hL; exact hL)] at this
    nlinarith
  have h2 : (1 + κ) ^ (M + 1) ≤ (1 + κ) ^ ν := pow_le_pow_right₀ (by linarith) hν1
  linarith

/-- `(M + c)^N / r^{M+1} → 0` for `r > 1`. -/
theorem tendsto_poly_div_exp {r : ℝ} (hr : 1 < r) (c : ℝ) (N : ℕ) :
    Tendsto (fun M : ℕ => ((M : ℝ) + c) ^ N / r ^ (M + 1)) atTop (𝓝 0) := by
  have hr0 : 0 < r := by linarith
  have key : Tendsto (fun M : ℕ => (M : ℝ) ^ N / r ^ M) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt N hr
  -- `(M + c)^N ≤ 2^N M^N` eventually
  have hbound : ∀ᶠ M : ℕ in atTop,
      ‖((M : ℝ) + c) ^ N / r ^ (M + 1)‖ ≤ (2 ^ N / r) * ((M : ℝ) ^ N / r ^ M) := by
    filter_upwards [eventually_ge_atTop (⌈|c|⌉₊)] with M hM
    have hM' : |c| ≤ (M : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hM)
    have hc1 : 0 ≤ (M : ℝ) + c := by linarith [neg_abs_le c]
    have hc2 : (M : ℝ) + c ≤ 2 * M := by linarith [le_abs_self c]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_succ]
    have hp : ((M : ℝ) + c) ^ N ≤ (2 * M) ^ N := pow_le_pow_left₀ hc1 hc2 N
    rw [mul_pow] at hp
    have hrM : 0 < r ^ M := pow_pos hr0 M
    calc ((M : ℝ) + c) ^ N / (r ^ M * r) ≤ 2 ^ N * (M : ℝ) ^ N / (r ^ M * r) :=
          div_le_div_of_nonneg_right hp (by positivity)
      _ = (2 ^ N / r) * ((M : ℝ) ^ N / r ^ M) := by field_simp
  have hlim : Tendsto (fun M : ℕ => (2 ^ N / r) * ((M : ℝ) ^ N / r ^ M)) atTop (𝓝 0) := by
    simpa using key.const_mul (2 ^ N / r)
  exact squeeze_zero_norm' hbound hlim

/-- **Eventually certified.** For fixed `h`, disc `R`, eigenvalue configuration and size `B`, there
is `M₀` such that for every `M ≥ M₀` the bound `|S_ν| ≤ B q^{ν/2}` at the orders
`M+1, …, M+N` makes every trace point pure. -/
theorem eventually_isPureTrace_of_bounded_powerSums {ι : Type*} {h : ℤ[X]} (hh : h.Monic) {q : ℕ}
    (hq : 1 ≤ q) {R : ℝ} (hR1 : 1 ≤ 2 * R) (hR : ∀ z ∈ (toC h).roots, ‖z‖ ≤ R) {s : Finset ι}
    {z : ι → ℂ} (hE : IsEigenConfig q h s z) (B : ℝ) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M →
      (∀ ν, M + 1 ≤ ν → ν ≤ M + s.card → ‖∑ i ∈ s, z i ^ ν‖ ≤ B * Real.sqrt q ^ ν) →
        ∀ τ ∈ (toC h).roots, IsPureTrace q τ := by
  -- choose `κ` below both quantization scales
  have hq0 : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr (by exact_mod_cast hq)
  have hR0 : 0 < 2 * R := by linarith
  have hgi : 0 < gapIm R h.natDegree := by unfold gapIm; positivity
  have hge : 0 < gapEdge q R h.natDegree := by
    unfold gapEdge
    have : 0 < R := by linarith
    positivity
  set κ : ℝ := min 1 (min (gapIm R h.natDegree / (8 * Real.sqrt q))
    (gapEdge q R h.natDegree / (2 * Real.sqrt q))) with hκ
  have hκ0 : 0 < κ := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hκim : 4 * Real.sqrt q * κ < gapIm R h.natDegree := by
    have : κ ≤ gapIm R h.natDegree / (8 * Real.sqrt q) :=
      (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hκedge : Real.sqrt q * κ < gapEdge q R h.natDegree := by
    have : κ ≤ gapEdge q R h.natDegree / (2 * Real.sqrt q) :=
      (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  by_cases hs : s.card = 0
  · -- no eigenvalues: no trace points
    refine ⟨0, fun M _ _ τ hτ => ?_⟩
    obtain ⟨i, hi, -⟩ := hE.cover τ hτ
    exact absurd (Finset.card_eq_zero.mp hs ▸ hi) (Finset.notMem_empty i)
  have hN : 1 ≤ s.card := Nat.one_le_iff_ne_zero.mpr hs
  -- `B · L_N(M) / (1+κ)^{M+1} → 0`
  set N := s.card
  have hlim : Tendsto (fun M : ℕ => B * turanConst N M / (1 + κ) ^ (M + 1)) atTop (𝓝 0) := by
    have hT : ∀ M : ℕ, B * turanConst N M / (1 + κ) ^ (M + 1) =
        (B * (2 * (Real.exp 1 * N * (6 * (N + 1)) ^ N))) *
          (((M : ℝ) + (2 * N + 2)) ^ N / (1 + κ) ^ (M + 1)) := by
      intro M
      unfold turanConst
      rw [show (6 * ((N : ℝ) + 1) * ((M : ℝ) + 2 * N + 2)) =
          (6 * (N + 1)) * ((M : ℝ) + (2 * N + 2)) by ring, mul_pow]
      ring
    simp_rw [hT]
    simpa using (tendsto_poly_div_exp (by linarith : 1 < 1 + κ) (2 * N + 2) N).const_mul
      (B * (2 * (Real.exp 1 * N * (6 * (N + 1)) ^ N)))
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (zero_lt_one' ℝ)))
  refine ⟨M₀, fun M hM hS => ?_⟩
  have h1 := hM₀ M hM
  have hpos : 0 < (1 + κ) ^ (M + 1) := pow_pos (by linarith) _
  rw [div_lt_one hpos] at h1
  exact isPureTrace_of_bounded_powerSums hh hq hR1 hR hE hκ0 hκ1 hκim hκedge hS h1

/-- **Real configurations are never certified at finitely many orders.** For every `M` there is
`r > 1` with `|r^ν + r^{−ν}| ≤ 3` for all `ν ≤ M`, while the trace point `r + r⁻¹` is impure
(`q = 1`). -/
theorem not_certified_at_finitely_many_orders (M : ℕ) :
    ∃ r : ℝ, 1 < r ∧ (∀ ν ≤ M, ‖(r : ℂ) ^ ν + ((r : ℂ)⁻¹) ^ ν‖ ≤ 3) ∧
      ¬ IsPureTrace 1 ((r : ℂ) + (r : ℂ)⁻¹) := by
  set r : ℝ := 2 ^ ((1 : ℝ) / (M + 1)) with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by positivity)
  have hr0 : 0 < r := by linarith
  refine ⟨r, hr1, fun ν hν => ?_, ?_⟩
  · have hrν : r ^ ν ≤ 2 := by
      calc r ^ ν ≤ r ^ (M + 1) := pow_le_pow_right₀ hr1.le (by omega)
        _ = 2 := by
          rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          rw [show (1 : ℝ) / (M + 1) * ((M + 1 : ℕ) : ℝ) = 1 by push_cast; field_simp]
          simp
    have hinv : r⁻¹ ^ ν ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hr1.le)
    calc ‖(r : ℂ) ^ ν + ((r : ℂ)⁻¹) ^ ν‖ ≤ ‖(r : ℂ) ^ ν‖ + ‖((r : ℂ)⁻¹) ^ ν‖ := norm_add_le _ _
      _ = r ^ ν + r⁻¹ ^ ν := by
          rw [norm_pow, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      _ ≤ 3 := by linarith
  · rintro ⟨-, hle⟩
    have hre : ((r : ℂ) + (r : ℂ)⁻¹).re = r + r⁻¹ := by
      rw [add_re, ofReal_re, ← ofReal_inv, ofReal_re]
    rw [hre, Real.sqrt_one, mul_one] at hle
    have hpos : 0 < r + r⁻¹ := by positivity
    rw [abs_of_pos hpos] at hle
    have : 2 < r + r⁻¹ := by
      have hne : r ≠ 1 := hr1.ne'
      have h := sq_pos_of_pos (sub_pos.mpr hr1)
      rw [← sub_pos]
      have : r + r⁻¹ - 2 = (r - 1) ^ 2 / r := by field_simp; ring
      rw [this]; positivity
    linarith

/-- **Integral zeta functions have a depth gap.** If a trace point of a monic integer polynomial is
impure, some eigenvalue `α` has `|α| > √q(1+κ)`; for the zero `s` of the zeta function with
`q^s = α` this is `Re s − ½ = log(|α|/√q)/log q > log(1+κ)/log q`. -/
theorem exists_deep_eigenvalue_of_not_pure {ι : Type*} {h : ℤ[X]} (hh : h.Monic) {q : ℕ}
    (hq : 2 ≤ q) {R : ℝ} (hR1 : 1 ≤ 2 * R) (hR : ∀ z ∈ (toC h).roots, ‖z‖ ≤ R) {s : Finset ι}
    {z : ι → ℂ} (hE : IsEigenConfig q h s z) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hκim : 4 * Real.sqrt q * κ < gapIm R h.natDegree)
    (hκedge : Real.sqrt q * κ < gapEdge q R h.natDegree)
    (himp : ∃ τ ∈ (toC h).roots, ¬ IsPureTrace q τ) :
    ∃ i ∈ s, Real.log (1 + κ) / Real.log q < Real.log ‖z i‖ / Real.log q - 1 / 2 := by
  have hq1 : 1 ≤ q := by omega
  obtain ⟨i, hi, hbig⟩ : ∃ i ∈ s, Real.sqrt q * (1 + κ) < ‖z i‖ := by
    by_contra hsmall
    push Not at hsmall
    obtain ⟨τ, hτ, hnp⟩ := himp
    exact hnp (isPureTrace_of_eigen_bound hh hq1 hR1 hR hE hκ0 hκ1 hκim hκedge hsmall τ hτ)
  refine ⟨i, hi, ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hc : 0 < 1 + κ := by linarith
  have hlog : Real.log (Real.sqrt q * (1 + κ)) < Real.log ‖z i‖ :=
    Real.log_lt_log (mul_pos hs0 hc) hbig
  rw [Real.log_mul hs0.ne' hc.ne', Real.log_sqrt hq0.le] at hlog
  rw [div_lt_iff₀ hlogq, sub_mul, div_mul_cancel₀ _ hlogq.ne']
  linarith

end GaloisForLFunctions.ArithmeticDiscreteness
