import GaloisForLFunctions.RHTower.PolynomialFockAdaptedCenterSeparation
import GaloisForLFunctions.RHTower.CriticalPrimeKernelSchurSampling
import GaloisForLFunctions.HTGeometry.ShiftLatticeThetaSeries

/-!
# Bessel bound for adapted normalized tangent packets in the polynomial Fock space

The shifted adapted packets `φ_n` (`n ≥ 0`) are the unit-norm tangent vectors of the degree-`m`
polynomial moment Fock space centered at the adapted cell points `(n+1)^(2/m)`. Combining the
Gaussian overlap bound with the near/far lower bounds on the harmonic-curvature gap, the Gram
entries satisfy `|⟨φ_n, φ_k⟩| ≤ E_m(|n - k|)` for an explicit envelope
`E_m(d) = e^{2C/m} (exp(-a_m d²) + exp(-b_m d^(4/m)))`, which is summable over `ℤ` when `m > 4`.
A Schur row-sum test then gives a Bessel inequality for the packet family.

## Main results

- `summable_polynomialFockAdaptedGramEnvelope`: the envelope `d ↦ E_m(d)` is summable for `m > 4`.
- `norm_inner_polynomialFockShiftedAdaptedNormalizedTangentPacket_le`:
  `|⟨φ_n, φ_k⟩| ≤ E_m(dist n k)` for all `n, k`.
- `finset_gramRow_polynomialFockShiftedAdaptedNormalizedTangentPacket_le`: every finite Gram row
  sum `∑_{k ∈ T} |⟨φ_n, φ_k⟩|` is at most `Δ_m = ∑_{z ∈ ℤ} E_m(|z|)`.
- `summable_norm_inner_sq_polynomialFockShiftedAdaptedNormalizedTangentPacket`: for each `x`,
  `n ↦ |⟨φ_n, x⟩|²` is summable.
- `tsum_norm_inner_sq_polynomialFockShiftedAdaptedNormalizedTangentPacket_le`: the Bessel bound
  `∑_n |⟨φ_n, x⟩|² ≤ Δ_m ‖x‖²`.

## Hypotheses

All results are unconditional; the only parameter assumption is the strict range `4 < m`
(positivity of the envelope rates and its summability need `m > 4`).
-/

open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Near-diagonal Gaussian rate `a_m = m / (4 ((m/2) 2^(m/2 - 1))²)` of the Gram envelope. -/
def polynomialFockAdaptedNearGramRate (m : ℝ) : ℝ :=
  m / (4 * ((m / 2) * 2 ^ (m / 2 - 1)) ^ 2)

/-- Far-off-diagonal rate `b_m = (m/4) (1 - 2^(-2/m))²` of the Gram envelope. -/
def polynomialFockAdaptedFarGramRate (m : ℝ) : ℝ :=
  (m / 4) * (1 - 2 ^ (-(2 / m))) ^ 2

/-- Gram envelope `E_m(d) = exp(2C/m) (exp(-a_m d²) + exp(-b_m d^(4/m)))`, with `C` the local
Bregman constant of the degree-`m` potential. -/
def polynomialFockAdaptedGramEnvelope (m : ℝ) (d : ℕ) : ℝ :=
  Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
    (Real.exp (-(polynomialFockAdaptedNearGramRate m * (d : ℝ) ^ 2)) +
      Real.exp (-(polynomialFockAdaptedFarGramRate m * (d : ℝ) ^ (4 / m))))

/-- The adapted normalized tangent packet with index shifted by one, centered at `(n+1)^(2/m)`. -/
def polynomialFockShiftedAdaptedNormalizedTangentPacket
    (m : ℝ) (hm : 4 ≤ m) (n : ℕ) : MomentFock :=
  polynomialFockAdaptedNormalizedTangentPacket m hm (n + 1)

theorem polynomialFockAdaptedNearGramRate_pos
    {m : ℝ} (hm : 4 < m) : 0 < polynomialFockAdaptedNearGramRate m := by
  rw [polynomialFockAdaptedNearGramRate]
  positivity

theorem polynomialFockAdaptedFarGramRate_pos
    {m : ℝ} (hm : 4 < m) : 0 < polynomialFockAdaptedFarGramRate m := by
  have hm0 : 0 < m := by linarith
  have hα : 0 < 2 / m := by positivity
  have hlt : (2 : ℝ) ^ (-(2 / m)) < 1 := by
    rw [Real.rpow_neg (by norm_num), inv_lt_one_iff₀]
    right
    exact Real.one_lt_rpow_iff_of_pos (by norm_num) |>.2
      (Or.inl ⟨by norm_num, hα⟩)
  rw [polynomialFockAdaptedFarGramRate]
  exact mul_pos (by positivity) (sq_pos_of_pos (sub_pos.mpr hlt))

/-- For `4 < m` the Gram envelope is summable over `ℕ`. -/
theorem summable_polynomialFockAdaptedGramEnvelope
    {m : ℝ} (hm : 4 < m) :
    Summable (polynomialFockAdaptedGramEnvelope m) := by
  have hn := GaloisForLFunctions.HTGeometry.summable_rpow_mul_exp_neg_rpow
    (A := 0) (polynomialFockAdaptedNearGramRate_pos hm) (by norm_num : (0 : ℝ) < 2)
  have hf := GaloisForLFunctions.HTGeometry.summable_rpow_mul_exp_neg_rpow
    (A := 0) (polynomialFockAdaptedFarGramRate_pos hm) (by positivity : 0 < 4 / m)
  have hn' : Summable (fun n : ℕ =>
      Real.exp (-(polynomialFockAdaptedNearGramRate m * (n : ℝ) ^ 2))) := by
    simpa using hn
  have hf' : Summable (fun n : ℕ =>
      Real.exp (-(polynomialFockAdaptedFarGramRate m * (n : ℝ) ^ (4 / m)))) := by
    simpa using hf
  unfold polynomialFockAdaptedGramEnvelope
  exact (hn'.add hf').mul_left _

theorem polynomialFockAdaptedGramEnvelope_nonneg (m : ℝ) (d : ℕ) :
    0 ≤ polynomialFockAdaptedGramEnvelope m d := by
  unfold polynomialFockAdaptedGramEnvelope
  positivity

/-- For `4 < m` the two-sided envelope `z ↦ E_m(|z|)` is summable over `ℤ`. -/
theorem summable_int_polynomialFockAdaptedGramEnvelope_natAbs
    {m : ℝ} (hm : 4 < m) :
    Summable (fun z : ℤ => polynomialFockAdaptedGramEnvelope m z.natAbs) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor <;> simpa using summable_polynomialFockAdaptedGramEnvelope hm

/-- Assuming `4 < m` and `k ≤ n`, `|⟨φ_n, φ_k⟩| ≤ E_m(n - k)`; the near regime `n+1 ≤ 2(k+1)` uses
the quadratic gap bound and the far regime the `(n - k)^(4/m)` bound. -/
theorem norm_inner_polynomialFockShiftedAdaptedNormalizedTangentPacket_le_of_le
    {m : ℝ} (hm : 4 < m) {k n : ℕ} (hkn : k ≤ n) :
    ‖inner ℂ
        (polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le n)
        (polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le k)‖ ≤
      polynomialFockAdaptedGramEnvelope m (Nat.dist n k) := by
  let K : ℝ := (k + 1 : ℕ)
  let N : ℝ := (n + 1 : ℕ)
  let x : ℝ := N ^ (2 / m)
  let y : ℝ := K ^ (2 / m)
  let cx : ℝ := m * (1 + x ^ 2) ^ (m / 2 - 1)
  let cy : ℝ := m * (1 + y ^ 2) ^ (m / 2 - 1)
  let C : ℝ := polynomialFockLocalBregmanConstant m / m
  let H : ℝ := cx * cy / (2 * (cx + cy)) * (x - y) ^ 2
  let P : ℝ := 2 * Real.sqrt (cx * cy) / (cx + cy)
  let E : ℝ := Real.exp (2 * C)
  let D : ℝ := N - K
  have hm0 : 0 < m := by linarith
  have hK : 1 ≤ K := by dsimp [K]; exact_mod_cast Nat.le_add_left 1 k
  have hKN : K ≤ N := by dsimp [K, N]; exact_mod_cast Nat.add_le_add_right hkn 1
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one (hK.trans hKN)
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 _
  have hy0 : 0 < y := Real.rpow_pos_of_pos hK0 _
  have hcx : 0 < cx := by dsimp [cx]; positivity
  have hcy : 0 < cy := by dsimp [cy]; positivity
  have hsum : 0 < cx + cy := add_pos hcx hcy
  have hover :=
    norm_inner_polynomialMomentFockNormalizedTangentVector_le_gaussianOverlap
      hm.le hx0.le hy0.le
  have hover' :
      ‖inner ℂ
          (polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le n)
          (polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le k)‖ ≤
        P * E * Real.exp (-H) := by
    simpa [polynomialFockShiftedAdaptedNormalizedTangentPacket,
      polynomialFockAdaptedNormalizedTangentPacket,
      criticalPrimeFockAdaptedCellCenter, K, N, x, y, cx, cy, C, H, P, E]
      using hover
  have hpre : P ≤ 1 := by
    have hsqrt : Real.sqrt (cx * cy) = Real.sqrt cx * Real.sqrt cy :=
      Real.sqrt_mul hcx.le cy
    have hsx : Real.sqrt cx ^ 2 = cx := Real.sq_sqrt hcx.le
    have hsy : Real.sqrt cy ^ 2 = cy := Real.sq_sqrt hcy.le
    have hamgm : 2 * Real.sqrt (cx * cy) ≤ cx + cy := by
      rw [hsqrt]
      nlinarith [sq_nonneg (Real.sqrt cx - Real.sqrt cy)]
    dsimp [P]
    exact (div_le_one hsum).2 hamgm
  have hstrip :
      ‖inner ℂ
          (polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le n)
          (polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le k)‖ ≤
        E * Real.exp (-H) := by
    calc
      _ ≤ P * E * Real.exp (-H) := hover'
      _ = P * (E * Real.exp (-H)) := by ring
      _ ≤ 1 * (E * Real.exp (-H)) :=
        mul_le_mul_of_nonneg_right hpre (by positivity)
      _ = E * Real.exp (-H) := one_mul _
  have hdist : ((Nat.dist n k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hkn, Nat.cast_sub hkn]
  have hDdist : D = ((Nat.dist n k : ℕ) : ℝ) := by
    dsimp [D, N, K]
    rw [hdist]
    push_cast
    ring
  by_cases hnear : N ≤ 2 * K
  · have hH := polynomialFockHarmonicCurvatureGap_lower_near hm.le hK hKN hnear
    have hH' : polynomialFockAdaptedNearGramRate m * D ^ 2 ≤ H := by
      simpa [polynomialFockAdaptedNearGramRate, D, H, K, N, x, y, cx, cy] using hH
    have hexp : Real.exp (-H) ≤
        Real.exp (-(polynomialFockAdaptedNearGramRate m * D ^ 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ E * Real.exp (-H) := hstrip
      _ ≤ E * Real.exp (-(polynomialFockAdaptedNearGramRate m * D ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ E * (Real.exp (-(polynomialFockAdaptedNearGramRate m * D ^ 2)) +
          Real.exp (-(polynomialFockAdaptedFarGramRate m * D ^ (4 / m)))) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
      _ = polynomialFockAdaptedGramEnvelope m (Nat.dist n k) := by
        rw [polynomialFockAdaptedGramEnvelope, ← hDdist]
  · have hfar : 2 * K ≤ N := by linarith
    have hH := polynomialFockHarmonicCurvatureGap_lower_far hm.le hK hfar
    have hH' : polynomialFockAdaptedFarGramRate m * D ^ (4 / m) ≤ H := by
      simpa [polynomialFockAdaptedFarGramRate, D, H, K, N, x, y, cx, cy] using hH
    have hexp : Real.exp (-H) ≤
        Real.exp (-(polynomialFockAdaptedFarGramRate m * D ^ (4 / m))) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ E * Real.exp (-H) := hstrip
      _ ≤ E * Real.exp (-(polynomialFockAdaptedFarGramRate m * D ^ (4 / m))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ E * (Real.exp (-(polynomialFockAdaptedNearGramRate m * D ^ 2)) +
          Real.exp (-(polynomialFockAdaptedFarGramRate m * D ^ (4 / m)))) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
      _ = polynomialFockAdaptedGramEnvelope m (Nat.dist n k) := by
        rw [polynomialFockAdaptedGramEnvelope, ← hDdist]

/-- Assuming `4 < m`, the Gram entries of the shifted adapted packets satisfy
`|⟨φ_n, φ_k⟩| ≤ E_m(dist n k)`. -/
theorem norm_inner_polynomialFockShiftedAdaptedNormalizedTangentPacket_le
    {m : ℝ} (hm : 4 < m) (n k : ℕ) :
    ‖inner ℂ
        (polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le n)
        (polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le k)‖ ≤
      polynomialFockAdaptedGramEnvelope m (Nat.dist n k) := by
  rcases le_total k n with hkn | hnk
  · exact norm_inner_polynomialFockShiftedAdaptedNormalizedTangentPacket_le_of_le hm hkn
  · have h :=
      norm_inner_polynomialFockShiftedAdaptedNormalizedTangentPacket_le_of_le hm hnk
    rw [← inner_conj_symm, RCLike.norm_conj] at h
    simpa [Nat.dist_comm] using h

/-- Assuming `4 < m`, every finite Gram row sum `∑_{k ∈ T} |⟨φ_n, φ_k⟩|` is bounded by
`∑_{z ∈ ℤ} E_m(|z|)`, uniformly in `n` and `T`. -/
theorem finset_gramRow_polynomialFockShiftedAdaptedNormalizedTangentPacket_le
    {m : ℝ} (hm : 4 < m) (n : ℕ) (T : Finset ℕ) :
    ∑ k ∈ T,
        ‖inner ℂ
          (polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le n)
          (polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le k)‖ ≤
      ∑' z : ℤ, polynomialFockAdaptedGramEnvelope m z.natAbs := by
  let shift : ℕ → ℤ := fun k => (k : ℤ) - (n : ℤ)
  have hshift : Function.Injective shift := by
    intro a b hab
    dsimp [shift] at hab
    omega
  have habs : ∀ k : ℕ, (shift k).natAbs = Nat.dist n k := by
    intro k
    dsimp [shift]
    rcases le_total n k with hnk | hkn
    · rw [Int.natAbs_natCast_sub_natCast_of_ge hnk, Nat.dist_eq_sub_of_le hnk]
    · rw [Int.natAbs_natCast_sub_natCast_of_le hkn, Nat.dist_comm,
        Nat.dist_eq_sub_of_le hkn]
  have hle :
      ∑ k ∈ T,
          ‖inner ℂ
            (polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le n)
            (polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le k)‖ ≤
        ∑ k ∈ T, polynomialFockAdaptedGramEnvelope m (shift k).natAbs := by
    exact Finset.sum_le_sum fun k _ => by
      simpa [habs k] using
        norm_inner_polynomialFockShiftedAdaptedNormalizedTangentPacket_le hm n k
  calc
    _ ≤ ∑ k ∈ T, polynomialFockAdaptedGramEnvelope m (shift k).natAbs := hle
    _ = ∑ z ∈ T.image shift, polynomialFockAdaptedGramEnvelope m z.natAbs := by
      symm
      exact Finset.sum_image (fun _ _ _ _ h => hshift h)
    _ ≤ ∑' z : ℤ, polynomialFockAdaptedGramEnvelope m z.natAbs :=
      (summable_int_polynomialFockAdaptedGramEnvelope_natAbs hm).sum_le_tsum
        (T.image shift) (fun z _ => polynomialFockAdaptedGramEnvelope_nonneg m z.natAbs)

/-- Assuming `4 < m`, `n ↦ |⟨φ_n, x⟩|²` is summable for every `x` in the moment Fock space. -/
theorem summable_norm_inner_sq_polynomialFockShiftedAdaptedNormalizedTangentPacket
    {m : ℝ} (hm : 4 < m) (x : MomentFock) :
    Summable fun n =>
      ‖inner ℂ (polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le n) x‖ ^ 2 := by
  let φ : ℕ → MomentFock :=
    polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le
  let Δ : ℝ := ∑' z : ℤ, polynomialFockAdaptedGramEnvelope m z.natAbs
  have hΔ : 0 ≤ Δ := tsum_nonneg fun z =>
    polynomialFockAdaptedGramEnvelope_nonneg m z.natAbs
  have hrow : ∀ (r : ℕ) (T : Finset ℕ),
      ∑ t ∈ T, ‖inner ℂ (φ r) (φ t)‖ ≤ Δ := by
    exact finset_gramRow_polynomialFockShiftedAdaptedNormalizedTangentPacket_le hm
  exact summable_norm_inner_sq_of_forall_finset_gram_row_le
    (H := MomentFock) (ι := ℕ) φ hΔ hrow x

/-- Bessel inequality: assuming `4 < m`, `∑_n |⟨φ_n, x⟩|² ≤ (∑_{z ∈ ℤ} E_m(|z|)) ‖x‖²`. -/
theorem tsum_norm_inner_sq_polynomialFockShiftedAdaptedNormalizedTangentPacket_le
    {m : ℝ} (hm : 4 < m) (x : MomentFock) :
    ∑' n,
        ‖inner ℂ (polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le n) x‖ ^ 2 ≤
      (∑' z : ℤ, polynomialFockAdaptedGramEnvelope m z.natAbs) * ‖x‖ ^ 2 := by
  let φ : ℕ → MomentFock :=
    polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le
  let Δ : ℝ := ∑' z : ℤ, polynomialFockAdaptedGramEnvelope m z.natAbs
  have hΔ : 0 ≤ Δ := tsum_nonneg fun z =>
    polynomialFockAdaptedGramEnvelope_nonneg m z.natAbs
  have hrow : ∀ (r : ℕ) (T : Finset ℕ),
      ∑ t ∈ T, ‖inner ℂ (φ r) (φ t)‖ ≤ Δ := by
    exact finset_gramRow_polynomialFockShiftedAdaptedNormalizedTangentPacket_le hm
  exact tsum_norm_inner_sq_le_of_forall_finset_gram_row_le
    (H := MomentFock) (ι := ℕ) φ hΔ hrow x

end

end RHTower
