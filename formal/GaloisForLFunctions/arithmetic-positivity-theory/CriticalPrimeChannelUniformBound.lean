import GaloisForLFunctions.«arithmetic-positivity-theory».CollaredCriticalPrimeChannelUniformBound

/-!
# The critical prime channel is bounded on `ℓ²`

On a dyadic scale block, the critical prime atoms are
`Λ(r) r^{-1} ∫_{v>1} v^{-2} B_b(v) B_b(rv) dv`. Split `v^{-2} = ψ + φ_e` into the collar weight
`ψ = σ(v - 1)/v²`, which is flat at `v = 1`, and the endpoint weight `φ_e = (1 - σ(v - 1))/v²`. The
endpoint weight lives on `[1, 2]` and jumps by `1` at `v = 1`.

* Two integrations by parts on `[1, 2]` split its cosine transform as `F_{φ_e} = j + e`. Here
  `j(f) = -sin(2πf)/(2πf)` is the **jump kernel** and `|e(f)| ≤ κ_e/f²`.
* The jump kernel is the average `-(1/2)∫_{-1}^{1} cos(2πfu) du`. Its bilinear form over two
  separated frequency families therefore splits by Cauchy–Schwarz into two mean squares of
  exponential sums over `[-1, 1]`. The Montgomery–Vaughan interval inequality bounds each of them
  by `(2 + 26/(πD)) ∑ b_n²`, with no separation needed between the two families. Away from the
  resonance `k ≈ lr` the trivial `1/f` bound suffices.
* With the harmonic reduction of the dyadic dilation inequality, the endpoint correlations decay
  like `r^{-1/2}`, exactly as the collared ones.

Hence `|∑_r Λ(r) r^{-1/2} ac(log r)| ≤ C_P ∑ b_n²` on every dyadic block, uniformly in the scale,
the number and the positions of the atoms. The Hilbert-type `1/f` tail of the endpoint jump is the
only obstruction to `ℓ²`-uniformity, and it is removed by the Montgomery–Vaughan inequality.
-/

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ### The jump kernel -/

/-- **Jump kernel** `j(f) = -(1/2) ∫_{-1}^{1} cos(2πfu) du = -sin(2πf)/(2πf)`: the `1/f` part of the
cosine transform of a weight with a unit jump at `v = 1`. -/
def dyadicJumpKernel (f : ℝ) : ℝ := -(1 / 2) * ∫ u in (-1 : ℝ)..1, Real.cos (2 * Real.pi * f * u)

theorem dyadicJumpKernel_eq {f : ℝ} (hf : f ≠ 0) :
    dyadicJumpKernel f = -(Real.sin (2 * Real.pi * f) / (2 * Real.pi * f)) := by
  have hc : 2 * Real.pi * f ≠ 0 := mul_ne_zero (by positivity) hf
  unfold dyadicJumpKernel
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos, smul_eq_mul,
    mul_neg_one, mul_one, Real.sin_neg]
  field_simp
  ring

theorem abs_dyadicJumpKernel_le_one (f : ℝ) : |dyadicJumpKernel f| ≤ 1 := by
  unfold dyadicJumpKernel
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1) (C := 1)
    (f := fun u => Real.cos (2 * Real.pi * f * u)) fun u _ => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  rw [Real.norm_eq_abs] at h
  rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  norm_num at h ⊢
  linarith

theorem abs_dyadicJumpKernel_le_inv {f : ℝ} (hf : f ≠ 0) :
    |dyadicJumpKernel f| ≤ 1 / (2 * Real.pi * |f|) := by
  rw [dyadicJumpKernel_eq hf, abs_neg, abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
    abs_two]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)

/-- The exponential sum `∑_{n ∈ S} b_n e^{2πi x_n u}` over a finite family. -/
private def jumpExpSum (S : Finset ℕ) (b x : ℕ → ℝ) (u : ℝ) : ℂ :=
  ∑ r : S, (b r : ℂ) * HTGeometry.mvExp (x r) u

private theorem continuous_jumpExpSum (S : Finset ℕ) (b x : ℕ → ℝ) : Continuous (jumpExpSum S b x) := by
  unfold jumpExpSum
  exact continuous_finsetSum _ fun r _ => continuous_const.mul (HTGeometry.continuous_mvExp _)

private theorem re_jumpExpSum_mul_conj (S : Finset ℕ) (b x y : ℕ → ℝ) (u : ℝ) :
    (jumpExpSum S b x u * conj (jumpExpSum S b y u)).re =
      ∑ n ∈ S, ∑ n' ∈ S, b n * b n' * Real.cos (2 * Real.pi * (x n - y n') * u) := by
  unfold jumpExpSum
  rw [map_sum, Finset.sum_mul_sum, Complex.re_sum, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Complex.re_sum, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, Complex.conj_ofReal,
    show (b r : ℂ) * HTGeometry.mvExp (x r) u * ((b s : ℂ) * conj (HTGeometry.mvExp (y s) u)) =
      ((b r * b s : ℝ) : ℂ) * (HTGeometry.mvExp (x r) u * conj (HTGeometry.mvExp (y s) u)) by
        push_cast; ring,
    HTGeometry.mvExp_mul_conj_mvExp, Complex.re_ofReal_mul, Complex.exp_re]
  congr 1
  have hre : ((2 * Real.pi * Complex.I * ((x r - y s : ℝ) : ℂ)) * (u : ℂ)).re = 0 := by simp
  have him : ((2 * Real.pi * Complex.I * ((x r - y s : ℝ) : ℂ)) * (u : ℂ)).im =
      2 * Real.pi * (x r - y s) * u := by simp
  rw [hre, him, Real.exp_zero, one_mul]

/-- **Montgomery–Vaughan bound for the jump kernel.** For two `D`-separated frequency families on
`S`, `|∑_{n,n'} b_n b_{n'} j(x_n - y_{n'})| ≤ (1 + 13/(πD)) ∑ b_n²`: the sinc kernel is an average
of exponentials over `[-1, 1]`, Cauchy–Schwarz splits the two families, and each mean square is
bounded by the Montgomery–Vaughan interval inequality. No separation between the families is
needed. -/
theorem abs_bilinear_dyadicJumpKernel_le {S : Finset ℕ} (b : ℕ → ℝ) {x y : ℕ → ℝ} {D : ℝ}
    (hD : 0 < D) (hx : ∀ n ∈ S, ∀ m ∈ S, n ≠ m → D ≤ |x n - x m|)
    (hy : ∀ n ∈ S, ∀ m ∈ S, n ≠ m → D ≤ |y n - y m|) :
    |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicJumpKernel (x n - y n')| ≤
      (1 + 13 / (Real.pi * D)) * ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  set A := jumpExpSum S b x
  set B := jumpExpSum S b y
  have hcA := continuous_jumpExpSum S b x
  have hcB := continuous_jumpExpSum S b y
  have hmv (z : ℕ → ℝ) (hz : ∀ n ∈ S, ∀ m ∈ S, n ≠ m → D ≤ |z n - z m|) :
      (∫ u in (-1 : ℝ)..1, ‖jumpExpSum S b z u‖ ^ 2) ≤ (2 + 26 / (Real.pi * D)) * E := by
    have h := HTGeometry.interval_integral_normSq_expSum_le (ι := S) (fun r => z r)
      (fun r => (b r : ℂ)) (a := -1) (ℓ := 2) hD fun r s hrs =>
        hz r r.2 s s.2 fun h => hrs (Subtype.ext h)
    rw [show (-1 : ℝ) + 2 = 1 by norm_num] at h
    have hE : ∑ r : S, ‖(b r : ℂ)‖ ^ (2 : ℕ) = E := by
      rw [Finset.sum_coe_sort S (fun n => ‖(b n : ℂ)‖ ^ (2 : ℕ))]
      exact Finset.sum_congr rfl fun n _ => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hE] at h
    exact h
  have hbil : ∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicJumpKernel (x n - y n') =
      -(1 / 2) * ∫ u in (-1 : ℝ)..1, (A u * conj (B u)).re := by
    have hre : (fun u => (A u * conj (B u)).re) = fun u =>
        ∑ n ∈ S, ∑ n' ∈ S, b n * b n' * Real.cos (2 * Real.pi * (x n - y n') * u) :=
      funext fun u => re_jumpExpSum_mul_conj S b x y u
    rw [hre, intervalIntegral.integral_finsetSum fun n _ => ?_]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [intervalIntegral.integral_finsetSum fun n' _ => ?_]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n' _ => ?_
        unfold dyadicJumpKernel
        rw [intervalIntegral.integral_const_mul]
        ring_nf
      · exact (by fun_prop : Continuous fun u => b n * b n' *
          Real.cos (2 * Real.pi * (x n - y n') * u)).intervalIntegrable _ _
    · exact (continuous_finsetSum _ fun n' _ => (by fun_prop : Continuous fun u => b n * b n' *
          Real.cos (2 * Real.pi * (x n - y n') * u))).intervalIntegrable _ _
  have hpt (u : ℝ) : |(A u * conj (B u)).re| ≤ (‖A u‖ ^ 2 + ‖B u‖ ^ 2) / 2 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    nlinarith [sq_nonneg (‖A u‖ - ‖B u‖)]
  have hcont : Continuous fun u => (A u * conj (B u)).re :=
    Complex.continuous_re.comp (hcA.mul (Complex.continuous_conj.comp hcB))
  have hcA2 : Continuous fun u => ‖A u‖ ^ 2 := hcA.norm.pow 2
  have hcB2 : Continuous fun u => ‖B u‖ ^ 2 := hcB.norm.pow 2
  have hint : |∫ u in (-1 : ℝ)..1, (A u * conj (B u)).re| ≤
      ((∫ u in (-1 : ℝ)..1, ‖A u‖ ^ 2) + ∫ u in (-1 : ℝ)..1, ‖B u‖ ^ 2) / 2 := by
    rw [← intervalIntegral.integral_add (hcA2.intervalIntegrable _ _) (hcB2.intervalIntegrable _ _),
      ← intervalIntegral.integral_div]
    refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans ?_
    exact intervalIntegral.integral_mono_on (by norm_num) (hcont.abs.intervalIntegrable _ _)
      ((hcA2.add hcB2).div_const 2 |>.intervalIntegrable _ _) fun u _ => hpt u
  rw [hbil, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h1 := hmv x hx
  have h2 := hmv y hy
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc 1 / 2 * |∫ u in (-1 : ℝ)..1, (A u * conj (B u)).re| ≤
        1 / 2 * (((2 + 26 / (Real.pi * D)) * E + (2 + 26 / (Real.pi * D)) * E) / 2) := by
        gcongr
        exact hint.trans (by gcongr)
    _ = (1 + 13 / (Real.pi * D)) * E := by ring

/-! ### The jump part of the cross-scale kernel -/

/-- The cross-scale kernel is additive in the transform. -/
theorem dyadicCrossKernel_add (F G : ℝ → ℝ) (p q : ℝ) (n n' : ℕ) :
    dyadicCrossKernel (fun f => F f + G f) p q n n' =
      dyadicCrossKernel F p q n n' + dyadicCrossKernel G p q n n' := by
  unfold dyadicCrossKernel
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A dilated scale branch is `11/12`-separated: `|pθ_n - pθ_m| ≥ 11/12` for distinct scales and
`p ≥ 1`. -/
theorem dilated_scaleBranch_sep {p : ℝ} (hp : 1 ≤ p) (i : Bool) (S : Finset ℕ) :
    ∀ n ∈ S, ∀ m ∈ S, n ≠ m → 11 / 12 ≤ |p * scaleBranch i n - p * scaleBranch i m| := by
  intro n _ m _ hnm
  have h := scaleBranch_spacing i n m
  have h1 : (1 : ℝ) ≤ |(n : ℝ) - m| := by
    rcases Nat.lt_or_gt_of_ne hnm with h | h
    · exact le_abs.mpr (Or.inr (by have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
                                   linarith))
    · exact le_abs.mpr (Or.inl (by have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
                                   linarith))
  rw [← mul_sub, abs_mul, abs_of_pos (by linarith)]
  nlinarith [abs_nonneg (scaleBranch i n - scaleBranch i m)]

private theorem sum_sum_bool_comm (S : Finset ℕ) (T : Bool → Bool → ℕ → ℕ → ℝ) :
    ∑ n ∈ S, ∑ n' ∈ S, ∑ i : Bool, ∑ j : Bool, T i j n n' =
      ∑ i : Bool, ∑ j : Bool, ∑ n ∈ S, ∑ n' ∈ S, T i j n n' := by
  simp only [Fintype.sum_bool, Finset.sum_add_distrib]

/-- Resonance-localised bound of the jump bilinear form: `4(1 + 13·12/(11π))` near `p ≈ q`,
`16/(π max(p, q))` away from it. -/
def jumpResonanceBound (p q : ℝ) : ℝ :=
  if q < 4 * p ∧ p < 4 * q then 4 * (1 + 13 / (Real.pi * (11 / 12))) else 16 / (Real.pi * max p q)

theorem jumpResonanceBound_nonneg {p q : ℝ} (hp : 1 ≤ p) : 0 ≤ jumpResonanceBound p q := by
  unfold jumpResonanceBound
  have : 0 < max p q := lt_of_lt_of_le (by linarith) (le_max_left p q)
  split_ifs <;> positivity

/-- **Jump cross-kernel on a dyadic block.** For harmonic frequencies `p, q ≥ 1`, the bilinear form
of the jump cross-kernel is at most `J(p, q) ∑ b_n²`: Montgomery–Vaughan near resonance, the
trivial `1/f` bound away from it. -/
theorem abs_bilinear_dyadicCrossKernel_jump_le {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M)
    (hS : DyadicScaleBlock S M) {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (b : ℕ → ℝ) :
    |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel dyadicJumpKernel p q n n'| ≤
      jumpResonanceBound p q * ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set θ := scaleBranch
  set Im : Bool → Bool → ℝ := fun i j =>
    ∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicJumpKernel (p * θ i n - q * θ j n')
  set Ip : Bool → Bool → ℝ := fun i j =>
    ∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicJumpKernel (p * θ i n + q * θ j n')
  have hexp : ∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel dyadicJumpKernel p q n n' =
      ∑ i : Bool, ∑ j : Bool, scaleBranchSign i * scaleBranchSign j / 2 * (Im i j + Ip i j) := by
    simp only [dyadicCrossKernel, Finset.mul_sum]
    rw [sum_sum_bool_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Im, Ip, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
    ring
  have hsgn (i j : Bool) : |scaleBranchSign i * scaleBranchSign j / 2| = 1 / 2 := by
    unfold scaleBranchSign; cases i <;> cases j <;> norm_num
  have htri : |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel dyadicJumpKernel p q n n'| ≤
      ∑ i : Bool, ∑ j : Bool, 1 / 2 * (|Im i j| + |Ip i j|) := by
    rw [hexp]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, hsgn]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  unfold jumpResonanceBound
  split_ifs with hnear
  · -- near resonance: Montgomery–Vaughan for both signs
    set c := 1 + 13 / (Real.pi * (11 / 12))
    have hIm (i j : Bool) : |Im i j| ≤ c * E :=
      abs_bilinear_dyadicJumpKernel_le b (x := fun n => p * θ i n) (y := fun n => q * θ j n)
        (by norm_num) (dilated_scaleBranch_sep hp i S) (dilated_scaleBranch_sep hq j S)
    have hIp (i j : Bool) : |Ip i j| ≤ c * E := by
      have h := abs_bilinear_dyadicJumpKernel_le b (S := S) (x := fun n => p * θ i n)
        (y := fun n => -(q * θ j n)) (D := 11 / 12) (by norm_num) (dilated_scaleBranch_sep hp i S)
        (fun n hn m hm hnm => by
          rw [show -(q * θ j n) - -(q * θ j m) = -(q * θ j n - q * θ j m) by ring, abs_neg]
          exact dilated_scaleBranch_sep hq j S n hn m hm hnm)
      simpa only [sub_neg_eq_add] using h
    refine htri.trans ?_
    calc ∑ i : Bool, ∑ j : Bool, 1 / 2 * (|Im i j| + |Ip i j|) ≤
          ∑ _i : Bool, ∑ _j : Bool, 1 / 2 * (c * E + c * E) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            gcongr
            · exact hIm i j
            · exact hIp i j
      _ = 4 * c * E := by simp only [Fintype.sum_bool]; ring
  · -- away from resonance every argument has size at least `max(p, q) M / 4`
    set m := max p q
    have hm1 : 1 ≤ m := hp.trans (le_max_left p q)
    have hfar : ∀ i j, ∀ n ∈ S, ∀ n' ∈ S, m * M / 4 ≤ |p * θ i n - q * θ j n'| ∧
        m * M / 4 ≤ |p * θ i n + q * θ j n'| := by
      intro i j n hn n' hn'
      have hx := scaleBranch_mem_block hM hS i hn
      have hy := scaleBranch_mem_block hM hS j hn'
      simp only [not_and_or, not_lt] at hnear
      rcases hnear with h | h
      · have hm : m = q := max_eq_right (by linarith)
        rw [hm]
        constructor
        · rw [abs_sub_comm]
          refine le_abs.mpr (Or.inl ?_)
          nlinarith [hx.1, hx.2, hy.1, hy.2]
        · refine le_abs.mpr (Or.inl ?_)
          nlinarith [hx.1, hx.2, hy.1, hy.2]
      · have hm : m = p := max_eq_left (by linarith)
        rw [hm]
        constructor
        · refine le_abs.mpr (Or.inl ?_)
          nlinarith [hx.1, hx.2, hy.1, hy.2]
        · refine le_abs.mpr (Or.inl ?_)
          nlinarith [hx.1, hx.2, hy.1, hy.2]
    have hjb {f : ℝ} (hf : m * M / 4 ≤ |f|) : |dyadicJumpKernel f| ≤ 2 / (Real.pi * m * M) := by
      have hf0 : f ≠ 0 := fun h => by rw [h, abs_zero] at hf; nlinarith
      refine (abs_dyadicJumpKernel_le_inv hf0).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_pos]
    have hcard : (∑ n ∈ S, |b n|) ^ 2 ≤ 2 * M * E := by
      have h1 : (∑ n ∈ S, |b n|) ^ 2 ≤ S.card * E := by
        simpa only [sq_abs] using (sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => |b i|))
      have h2 : (S.card : ℝ) ≤ 2 * M := by
        have := hS.card_le
        have : (S.card : ℝ) ≤ M + 1 := by exact_mod_cast this
        linarith
      nlinarith
    have hgen (F : ℕ → ℕ → ℝ) (hF : ∀ n ∈ S, ∀ n' ∈ S, |F n n'| ≤ 2 / (Real.pi * m * M)) :
        |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * F n n'| ≤ 4 / (Real.pi * m) * E := by
      calc |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * F n n'| ≤
            ∑ n ∈ S, ∑ n' ∈ S, |b n| * |b n'| * (2 / (Real.pi * m * M)) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n' hn' => ?_)
            rw [abs_mul, abs_mul]
            exact mul_le_mul_of_nonneg_left (hF n hn n' hn') (by positivity)
        _ = (∑ n ∈ S, |b n|) ^ 2 * (2 / (Real.pi * m * M)) := by
            rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.sum_mul]
        _ ≤ 2 * M * E * (2 / (Real.pi * m * M)) := by gcongr
        _ = 4 / (Real.pi * m) * E := by field_simp; ring
    have hIm (i j : Bool) : |Im i j| ≤ 4 / (Real.pi * m) * E :=
      hgen _ fun n hn n' hn' => hjb (hfar i j n hn n' hn').1
    have hIp (i j : Bool) : |Ip i j| ≤ 4 / (Real.pi * m) * E :=
      hgen _ fun n hn n' hn' => hjb (hfar i j n hn n' hn').2
    refine htri.trans ?_
    calc ∑ i : Bool, ∑ j : Bool, 1 / 2 * (|Im i j| + |Ip i j|) ≤
          ∑ _i : Bool, ∑ _j : Bool, 1 / 2 * (4 / (Real.pi * m) * E + 4 / (Real.pi * m) * E) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            gcongr
            · exact hIm i j
            · exact hIp i j
      _ = 16 / (Real.pi * m) * E := by simp only [Fintype.sum_bool]; ring

/-! ### The endpoint weight and its transform -/

/-- **Endpoint weight** `φ_e(v) = (1 - σ(v - 1))/v²`: the part of the critical weight `v^{-2}`
removed by the collar. On `(1, ∞)` it equals `1` at `v = 1⁺`, is smooth, and vanishes for `v ≥ 2`. -/
def criticalEndpointWeight (v : ℝ) : ℝ := (1 - Real.smoothTransition (v - 1)) / v ^ 2

theorem criticalEndpointWeight_one : criticalEndpointWeight 1 = 1 := by
  simp [criticalEndpointWeight, Real.smoothTransition.zero_of_nonpos le_rfl]

theorem criticalEndpointWeight_eq_zero {x : ℝ} (hx : 2 ≤ x) : criticalEndpointWeight x = 0 := by
  rw [criticalEndpointWeight, Real.smoothTransition.one_of_one_le (by linarith), sub_self, zero_div]

theorem criticalCollarWeight_add_criticalEndpointWeight {v : ℝ} (hv : 0 < v) :
    criticalCollarWeight v + criticalEndpointWeight v = v ^ (-2 : ℝ) := by
  rw [Real.rpow_neg hv.le, Real.rpow_two, criticalCollarWeight, criticalEndpointWeight, ← add_div,
    add_sub_cancel, one_div]

theorem contDiffOn_criticalEndpointWeight : ContDiffOn ℝ (⊤ : ℕ∞) criticalEndpointWeight (Ioi 0) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  exact ((contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (contDiff_id.sub contDiff_const))).contDiffAt.div (contDiff_id.pow 2).contDiffAt
      (pow_ne_zero 2 hx0)).contDiffWithinAt

theorem contDiffOn_deriv_criticalEndpointWeight :
    ContDiffOn ℝ (⊤ : ℕ∞) (deriv criticalEndpointWeight) (Ioi 0) :=
  contDiffOn_criticalEndpointWeight.deriv_of_isOpen isOpen_Ioi (by simp)

theorem hasDerivAt_criticalEndpointWeight {x : ℝ} (hx : 0 < x) :
    HasDerivAt criticalEndpointWeight (deriv criticalEndpointWeight x) x :=
  ((contDiffOn_criticalEndpointWeight.differentiableOn (by simp)).differentiableAt
    (isOpen_Ioi.mem_nhds hx)).hasDerivAt

theorem hasDerivAt_deriv_criticalEndpointWeight {x : ℝ} (hx : 0 < x) :
    HasDerivAt (deriv criticalEndpointWeight) (deriv (deriv criticalEndpointWeight) x) x :=
  ((contDiffOn_deriv_criticalEndpointWeight.differentiableOn (by simp)).differentiableAt
    (isOpen_Ioi.mem_nhds hx)).hasDerivAt

/-- The endpoint weight is flat at `v = 2`. -/
theorem deriv_criticalEndpointWeight_two : deriv criticalEndpointWeight 2 = 0 := by
  have hc : ContinuousAt (deriv criticalEndpointWeight) 2 :=
    (contDiffOn_deriv_criticalEndpointWeight.continuousOn).continuousAt (isOpen_Ioi.mem_nhds (show (2 : ℝ) ∈ Ioi 0 from mem_Ioi.mpr two_pos))
  have h1 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (2 : ℝ)))
  have h2 : Tendsto (deriv criticalEndpointWeight) (𝓝[>] 2) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have : criticalEndpointWeight =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds (show (2 : ℝ) < y from hy)] with z hz
      exact criticalEndpointWeight_eq_zero (le_of_lt hz)
    rw [this.deriv_eq, deriv_const]
  exact tendsto_nhds_unique h1 h2

theorem continuousOn_deriv_deriv_criticalEndpointWeight :
    ContinuousOn (deriv (deriv criticalEndpointWeight)) (Ioi 0) :=
  (contDiffOn_deriv_criticalEndpointWeight.deriv_of_isOpen isOpen_Ioi (m := 0) (by simp)).continuousOn

theorem integrableOn_criticalEndpointWeight : IntegrableOn criticalEndpointWeight (Ioi 1) := by
  rw [← Ioc_union_Ioi_eq_Ioi one_le_two]
  refine IntegrableOn.union ?_ ?_
  · exact ((contDiffOn_criticalEndpointWeight.continuousOn.mono fun x hx =>
      lt_of_lt_of_le one_pos hx.1).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · exact integrableOn_zero.congr_fun (fun x hx => (criticalEndpointWeight_eq_zero (le_of_lt hx)).symm)
      measurableSet_Ioi

/-- The endpoint transform is an integral over `[1, 2]`. -/
theorem weightCosineTransform_criticalEndpointWeight_eq (f : ℝ) :
    weightCosineTransform criticalEndpointWeight f =
      ∫ v in (1 : ℝ)..2, criticalEndpointWeight v * Real.cos (2 * Real.pi * f * v) := by
  have hint : IntegrableOn (fun v => criticalEndpointWeight v * Real.cos (2 * Real.pi * f * v)) (Ioi 1) :=
    integrableOn_criticalEndpointWeight.mul_bdd (by fun_prop : Continuous fun v =>
      Real.cos (2 * Real.pi * f * v)).aestronglyMeasurable
      (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  unfold weightCosineTransform
  rw [← Ioc_union_Ioi_eq_Ioi one_le_two, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set (Ioc_subset_Ioi_self)) (hint.mono_set (Ioi_subset_Ioi one_le_two)),
    intervalIntegral.integral_of_le one_le_two]
  have h0 : ∫ v in Ioi (2 : ℝ), criticalEndpointWeight v * Real.cos (2 * Real.pi * f * v) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun v hv => by
      rw [criticalEndpointWeight_eq_zero (le_of_lt hv), zero_mul]
  rw [h0, add_zero]

/-- Remainder `e(f) = F_{φ_e}(f) - j(f)` of the endpoint transform after its jump part. -/
def criticalEndpointRemainder (f : ℝ) : ℝ :=
  weightCosineTransform criticalEndpointWeight f - dyadicJumpKernel f

/-- **Two integrations by parts on `[1, 2]`.** For `ω = 2πf ≠ 0`,
`e(f) = -(φ_e'(1) cos ω + ∫_1^2 φ_e'' cos(ωv) dv)/ω²`: the jump `φ_e(1) = 1` produces exactly
`j(f)`, and flatness at `2` kills the other boundary terms. -/
theorem criticalEndpointRemainder_eq {f : ℝ} (hf : f ≠ 0) :
    criticalEndpointRemainder f = -(1 / (2 * Real.pi * f) ^ 2) *
      (deriv criticalEndpointWeight 1 * Real.cos (2 * Real.pi * f) +
        ∫ v in (1 : ℝ)..2, deriv (deriv criticalEndpointWeight) v * Real.cos (2 * Real.pi * f * v)) := by
  set ω := 2 * Real.pi * f with hω
  have hω0 : ω ≠ 0 := mul_ne_zero (by positivity) hf
  have hpos : ∀ x ∈ uIcc (1 : ℝ) 2, 0 < x := fun x hx => by
    rw [uIcc_of_le one_le_two] at hx; linarith [hx.1]
  have hsin (x : ℝ) : HasDerivAt (fun y => Real.sin (ω * y) / ω) (Real.cos (ω * x)) x :=
    ((((hasDerivAt_id' x).const_mul ω).sin).div_const ω).congr_deriv (by field_simp)
  have hcos (x : ℝ) : HasDerivAt (fun y => -Real.cos (ω * y) / ω) (Real.sin (ω * x)) x :=
    (((((hasDerivAt_id' x).const_mul ω).cos).neg).div_const ω).congr_deriv (by field_simp)
  have hcd : ContinuousOn (deriv criticalEndpointWeight) (uIcc 1 2) :=
    contDiffOn_deriv_criticalEndpointWeight.continuousOn.mono fun x hx => hpos x hx
  have hcdd : ContinuousOn (deriv (deriv criticalEndpointWeight)) (uIcc 1 2) :=
    continuousOn_deriv_deriv_criticalEndpointWeight.mono fun x hx => hpos x hx
  have e1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 1) (b := 2)
    (u := criticalEndpointWeight) (v := fun y => Real.sin (ω * y) / ω)
    (u' := deriv criticalEndpointWeight) (v' := fun y => Real.cos (ω * y))
    (fun x hx => hasDerivAt_criticalEndpointWeight (hpos x hx)) (fun x _ => hsin x)
    (hcd.intervalIntegrable) ((by fun_prop : Continuous fun y => Real.cos (ω * y)).intervalIntegrable _ _)
  have e2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 1) (b := 2)
    (u := deriv criticalEndpointWeight) (v := fun y => -Real.cos (ω * y) / ω)
    (u' := deriv (deriv criticalEndpointWeight)) (v' := fun y => Real.sin (ω * y))
    (fun x hx => hasDerivAt_deriv_criticalEndpointWeight (hpos x hx)) (fun x _ => hcos x)
    (hcdd.intervalIntegrable) ((by fun_prop : Continuous fun y => Real.sin (ω * y)).intervalIntegrable _ _)
  rw [criticalEndpointWeight_eq_zero le_rfl, criticalEndpointWeight_one] at e1
  rw [deriv_criticalEndpointWeight_two] at e2
  have e1' : ∫ x in (1 : ℝ)..2, deriv criticalEndpointWeight x * (Real.sin (ω * x) / ω) =
      1 / ω * ∫ x in (1 : ℝ)..2, deriv criticalEndpointWeight x * Real.sin (ω * x) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  have e2' : ∫ x in (1 : ℝ)..2, deriv (deriv criticalEndpointWeight) x * (-Real.cos (ω * x) / ω) =
      -(1 / ω) * ∫ x in (1 : ℝ)..2, deriv (deriv criticalEndpointWeight) x * Real.cos (ω * x) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  unfold criticalEndpointRemainder
  rw [weightCosineTransform_criticalEndpointWeight_eq, dyadicJumpKernel_eq hf]
  change (∫ x in (1 : ℝ)..2, criticalEndpointWeight x * Real.cos (ω * x)) - -(Real.sin ω / ω) = _
  rw [e1, e1', e2, e2']
  field_simp
  ring

/-- Curvature constant `(|φ_e'(1)| + ∫_1^2 |φ_e''|)/(4π²)` of the endpoint remainder. -/
def criticalEndpointCurvature : ℝ :=
  (|deriv criticalEndpointWeight 1| +
    ∫ v in (1 : ℝ)..2, |deriv (deriv criticalEndpointWeight) v|) / (4 * Real.pi ^ 2)

theorem criticalEndpointCurvature_nonneg : 0 ≤ criticalEndpointCurvature := by
  unfold criticalEndpointCurvature
  have : 0 ≤ ∫ v in (1 : ℝ)..2, |deriv (deriv criticalEndpointWeight) v| :=
    intervalIntegral.integral_nonneg one_le_two fun _ _ => abs_nonneg _
  positivity

theorem abs_criticalEndpointRemainder_le_div_sq {f : ℝ} (hf : f ≠ 0) :
    |criticalEndpointRemainder f| ≤ criticalEndpointCurvature / f ^ 2 := by
  have hpos : ∀ x ∈ uIcc (1 : ℝ) 2, 0 < x := fun x hx => by
    rw [uIcc_of_le one_le_two] at hx; linarith [hx.1]
  have hcdd : ContinuousOn (deriv (deriv criticalEndpointWeight)) (uIcc 1 2) :=
    continuousOn_deriv_deriv_criticalEndpointWeight.mono fun x hx => hpos x hx
  have hI : |∫ v in (1 : ℝ)..2, deriv (deriv criticalEndpointWeight) v * Real.cos (2 * Real.pi * f * v)| ≤
      ∫ v in (1 : ℝ)..2, |deriv (deriv criticalEndpointWeight) v| := by
    refine (intervalIntegral.abs_integral_le_integral_abs one_le_two).trans
      (intervalIntegral.integral_mono_on one_le_two ?_ hcdd.abs.intervalIntegrable fun v _ => ?_)
    · exact (hcdd.mul (by fun_prop : Continuous fun v =>
        Real.cos (2 * Real.pi * f * v)).continuousOn).abs.intervalIntegrable
    · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  rw [criticalEndpointRemainder_eq hf, abs_mul, abs_neg,
    abs_of_pos (by have := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hf; positivity :
      (0 : ℝ) < 1 / (2 * Real.pi * f) ^ 2)]
  have hb : |deriv criticalEndpointWeight 1 * Real.cos (2 * Real.pi * f) +
      ∫ v in (1 : ℝ)..2, deriv (deriv criticalEndpointWeight) v * Real.cos (2 * Real.pi * f * v)| ≤
      |deriv criticalEndpointWeight 1| + ∫ v in (1 : ℝ)..2, |deriv (deriv criticalEndpointWeight) v| := by
    refine (abs_add_le _ _).trans (add_le_add ?_ hI)
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  unfold criticalEndpointCurvature
  calc 1 / (2 * Real.pi * f) ^ 2 * |deriv criticalEndpointWeight 1 * Real.cos (2 * Real.pi * f) +
        ∫ v in (1 : ℝ)..2, deriv (deriv criticalEndpointWeight) v * Real.cos (2 * Real.pi * f * v)| ≤
        1 / (2 * Real.pi * f) ^ 2 * (|deriv criticalEndpointWeight 1| +
          ∫ v in (1 : ℝ)..2, |deriv (deriv criticalEndpointWeight) v|) := by gcongr
    _ = _ := by field_simp; ring

/-- Uniform bound `‖φ_e‖₁ + 1` of the endpoint remainder. -/
def criticalEndpointMass : ℝ := (∫ v in Ioi 1, |criticalEndpointWeight v|) + 1

theorem abs_criticalEndpointRemainder_le (f : ℝ) : |criticalEndpointRemainder f| ≤ criticalEndpointMass := by
  unfold criticalEndpointRemainder criticalEndpointMass
  refine (abs_sub _ _).trans (add_le_add ?_ (abs_dyadicJumpKernel_le_one f))
  unfold weightCosineTransform
  refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on ?_
    integrableOn_criticalEndpointWeight.abs measurableSet_Ioi fun v _ => ?_)
  · exact (integrableOn_criticalEndpointWeight.mul_bdd (by fun_prop : Continuous fun v =>
      Real.cos (2 * Real.pi * f * v)).aestronglyMeasurable
      (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)).abs
  · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-! ### The endpoint dilation bound -/

/-- Near-resonance constant `c_J = 1 + 13·12/(11π)` of the jump kernel. -/
private abbrev jumpNearConstant : ℝ := 1 + 13 / (Real.pi * (11 / 12))

private theorem weight_mul_jump_le {k l r : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hr : 1 ≤ r) :
    1 / (k : ℝ) ^ 2 * (1 / (l : ℝ) ^ 2) * jumpResonanceBound k ((l * r : ℕ) : ℝ) ≤
      1 / Real.sqrt r * (8 * jumpNearConstant * (1 / ((k : ℝ) * Real.sqrt k) * (1 / (l : ℝ) ^ 2)) +
        16 / Real.pi * (1 / (k : ℝ) ^ 2 * (1 / (l : ℝ) ^ 2))) := by
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl0 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hr0 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set q : ℝ := ((l * r : ℕ) : ℝ)
  have hq : q = l * r := by simp [q]
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr (by linarith)
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by linarith)
  have hc : 0 ≤ jumpNearConstant := by positivity
  have h1 : 0 ≤ 8 * jumpNearConstant * (1 / ((k : ℝ) * Real.sqrt k) * (1 / (l : ℝ) ^ 2)) := by positivity
  have h2 : 0 ≤ 16 / Real.pi * (1 / (k : ℝ) ^ 2 * (1 / (l : ℝ) ^ 2)) := by positivity
  unfold jumpResonanceBound
  split_ifs with hnear
  · have hsq : Real.sqrt r ≤ 2 * Real.sqrt k := by
      have h1 : Real.sqrt r ≤ Real.sqrt q := Real.sqrt_le_sqrt (by rw [hq]; nlinarith)
      have h2 : Real.sqrt q ≤ Real.sqrt (4 * k) := Real.sqrt_le_sqrt hnear.1.le
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h2
      linarith
    have hkk : (k : ℝ) ^ 2 = k * Real.sqrt k * Real.sqrt k := by
      rw [mul_assoc, Real.mul_self_sqrt (by linarith)]; ring
    have htrade : 1 / (k : ℝ) ^ 2 ≤ 2 / ((k : ℝ) * Real.sqrt k) * (1 / Real.sqrt r) := by
      rw [hkk, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos (by linarith : (0 : ℝ) < k) hsk]
    calc 1 / (k : ℝ) ^ 2 * (1 / (l : ℝ) ^ 2) * (4 * jumpNearConstant) ≤
          2 / ((k : ℝ) * Real.sqrt k) * (1 / Real.sqrt r) * (1 / (l : ℝ) ^ 2) * (4 * jumpNearConstant) := by
          gcongr
      _ = 1 / Real.sqrt r * (8 * jumpNearConstant * (1 / ((k : ℝ) * Real.sqrt k) * (1 / (l : ℝ) ^ 2))) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h2) (by positivity)
  · have hmax : Real.sqrt r ≤ max (k : ℝ) q := by
      have : Real.sqrt r ≤ r := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
      exact this.trans ((show (r : ℝ) ≤ q by rw [hq]; nlinarith).trans (le_max_right _ _))
    have hm0 : 0 < max (k : ℝ) q := lt_of_lt_of_le hsr hmax
    calc 1 / (k : ℝ) ^ 2 * (1 / (l : ℝ) ^ 2) * (16 / (Real.pi * max (k : ℝ) q)) ≤
          1 / (k : ℝ) ^ 2 * (1 / (l : ℝ) ^ 2) * (16 / (Real.pi * Real.sqrt r)) := by gcongr
      _ = 1 / Real.sqrt r * (16 / Real.pi * (1 / (k : ℝ) ^ 2 * (1 / (l : ℝ) ^ 2))) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h1) (by positivity)

/-- Summable majorant of the endpoint harmonic forms: the remainder part (as in the dyadic dilation
inequality) plus the jump part. -/
private def endpointMajorant (p : ℕ × ℕ) : ℝ :=
  (4 * (criticalEndpointMass + (80 * (Real.pi ^ 2 / 3) + 2) * criticalEndpointCurvature) *
      (1 / ((p.1 : ℝ) * Real.sqrt p.1) * (1 / (p.2 : ℝ) ^ 2)) +
    68 * criticalEndpointCurvature * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2))) +
  (8 * jumpNearConstant * (1 / ((p.1 : ℝ) * Real.sqrt p.1) * (1 / (p.2 : ℝ) ^ 2)) +
    16 / Real.pi * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2)))

/-- Endpoint dilation constant: the remainder part `K(‖φ_e‖₁ + 1, κ_e)` plus the jump part
`8 c_J (∑ k^{-3/2})(∑ l^{-2}) + (16/π)(∑ k^{-2})(∑ l^{-2})`. -/
def criticalEndpointDilationConstant : ℝ :=
  dyadicDilationConstant criticalEndpointMass criticalEndpointCurvature +
    (8 * jumpNearConstant * ((∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2) +
      16 / Real.pi * ((∑' k : ℕ, 1 / (k : ℝ) ^ 2) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2))

private theorem endpointMajorant_nonneg (p : ℕ × ℕ) : 0 ≤ endpointMajorant p := by
  have hB0 := criticalEndpointCurvature_nonneg
  have hA0 : 0 ≤ criticalEndpointMass := (abs_nonneg _).trans (abs_criticalEndpointRemainder_le 0)
  unfold endpointMajorant
  positivity

private theorem summable_endpointMajorant_and_tsum :
    Summable endpointMajorant ∧ ∑' p, endpointMajorant p = criticalEndpointDilationConstant := by
  have hz2 : Summable fun l : ℕ => 1 / (l : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
  have hs1 : Summable fun p : ℕ × ℕ => 1 / ((p.1 : ℝ) * Real.sqrt p.1) * (1 / (p.2 : ℝ) ^ 2) :=
    summable_inv_mul_sqrt.mul_of_nonneg hz2 (fun _ => by positivity) (fun _ => by positivity)
  have hs2 : Summable fun p : ℕ × ℕ => 1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) :=
    Summable.mul_of_nonneg (f := fun l : ℕ => 1 / (l : ℝ) ^ 2) (g := fun l : ℕ => 1 / (l : ℝ) ^ 2)
      hz2 hz2 (fun _ => by positivity) (fun _ => by positivity)
  have hn1 : Summable fun k : ℕ => ‖1 / ((k : ℝ) * Real.sqrt k)‖ :=
    summable_inv_mul_sqrt.abs.congr fun k => (Real.norm_eq_abs _).symm
  have hn2 : Summable fun l : ℕ => ‖1 / (l : ℝ) ^ 2‖ := hz2.abs.congr fun l => (Real.norm_eq_abs _).symm
  have hA := (hs1.mul_left (4 * (criticalEndpointMass + (80 * (Real.pi ^ 2 / 3) + 2) *
    criticalEndpointCurvature))).add (hs2.mul_left (68 * criticalEndpointCurvature))
  have hJ := (hs1.mul_left (8 * jumpNearConstant)).add (hs2.mul_left (16 / Real.pi))
  have heq : ∀ p, endpointMajorant p =
      ((4 * (criticalEndpointMass + (80 * (Real.pi ^ 2 / 3) + 2) * criticalEndpointCurvature) *
          (1 / ((p.1 : ℝ) * Real.sqrt p.1) * (1 / (p.2 : ℝ) ^ 2)) +
        68 * criticalEndpointCurvature * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2))) +
      (8 * jumpNearConstant * (1 / ((p.1 : ℝ) * Real.sqrt p.1) * (1 / (p.2 : ℝ) ^ 2)) +
        16 / Real.pi * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2)))) := fun p => rfl
  refine ⟨(hA.add hJ).congr fun p => (heq p).symm, ?_⟩
  rw [tsum_congr heq]
  unfold criticalEndpointDilationConstant dyadicDilationConstant
  rw [Summable.tsum_add hA hJ, Summable.tsum_add (hs1.mul_left _) (hs2.mul_left _),
    Summable.tsum_add (hs1.mul_left _) (hs2.mul_left _), tsum_mul_left, tsum_mul_left, tsum_mul_left,
    tsum_mul_left, tsum_mul_tsum_of_summable_norm hn1 hn2, tsum_mul_tsum_of_summable_norm hn2 hn2]

private theorem weightCosineTransform_criticalEndpointWeight_split :
    weightCosineTransform criticalEndpointWeight =
      fun f => dyadicJumpKernel f + criticalEndpointRemainder f := by
  funext f; unfold criticalEndpointRemainder; ring

private theorem endpoint_harmonic_le {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hS : DyadicScaleBlock S M)
    (b : ℕ → ℝ) {r : ℕ} (hr : 1 ≤ r) (p : ℕ × ℕ) (hk : 1 ≤ p.1) (hl : 1 ≤ p.2) :
    1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) *
      |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel
        (weightCosineTransform criticalEndpointWeight) p.1 ((p.2 * r : ℕ) : ℝ) n n'| ≤
      1 / Real.sqrt r * (∑ n ∈ S, b n ^ 2) * endpointMajorant p := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hB0 := criticalEndpointCurvature_nonneg
  have hA0 : 0 ≤ criticalEndpointMass := (abs_nonneg _).trans (abs_criticalEndpointRemainder_le 0)
  have hr' : (1 : ℝ) ≤ ((p.2 * r : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  set q : ℝ := ((p.2 * r : ℕ) : ℝ)
  have hk1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hk
  have hJ := abs_bilinear_dyadicCrossKernel_jump_le hM hS hk1 hr' b
  have hR := abs_bilinear_dyadicCrossKernel_le (F := criticalEndpointRemainder)
    abs_criticalEndpointRemainder_le (fun f hf => abs_criticalEndpointRemainder_le_div_sq hf)
    hB0 hM hS hk1 hr' b
  have hsplit : ∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel
      (weightCosineTransform criticalEndpointWeight) p.1 q n n' =
      ∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel dyadicJumpKernel p.1 q n n' +
      ∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel criticalEndpointRemainder p.1 q n n' := by
    rw [weightCosineTransform_criticalEndpointWeight_split, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n' _ => ?_
    rw [dyadicCrossKernel_add]; ring
  have hmaj := weight_mul_resonance_le hA0 hB0 hk hl hr
  have hjmaj := weight_mul_jump_le hk hl hr
  have hsum := (abs_add_le _ _).trans (add_le_add hJ hR)
  rw [← hsplit] at hsum
  set w := 1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2)
  have hw : 0 ≤ w := by positivity
  calc w * |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel
          (weightCosineTransform criticalEndpointWeight) p.1 q n n'| ≤
        w * (jumpResonanceBound p.1 q * E +
          2 * (dyadicResonanceBound criticalEndpointMass criticalEndpointCurvature p.1 q +
            2 * criticalEndpointCurvature / q ^ 2) * E) := mul_le_mul_of_nonneg_left hsum hw
    _ = E * (w * jumpResonanceBound p.1 q + w * (2 * (dyadicResonanceBound criticalEndpointMass
          criticalEndpointCurvature p.1 q + 2 * criticalEndpointCurvature / q ^ 2))) := by ring
    _ ≤ E * (1 / Real.sqrt r * (8 * jumpNearConstant * (1 / ((p.1 : ℝ) * Real.sqrt p.1) *
            (1 / (p.2 : ℝ) ^ 2)) + 16 / Real.pi * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2))) +
          1 / Real.sqrt r * (4 * (criticalEndpointMass + (80 * (Real.pi ^ 2 / 3) + 2) *
            criticalEndpointCurvature) * (1 / ((p.1 : ℝ) * Real.sqrt p.1) * (1 / (p.2 : ℝ) ^ 2)) +
            68 * criticalEndpointCurvature * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2)))) :=
        mul_le_mul_of_nonneg_left (add_le_add hjmaj hmaj) hE
    _ = 1 / Real.sqrt r * E * endpointMajorant p := by unfold endpointMajorant; ring

/-- **Endpoint dilation inequality.** For every finite family on a dyadic block and every `r ≥ 1`,
`|∫_{v>1} φ_e(v) B_b(v) B_b(rv) dv| ≤ (4/π⁴) K_e r^{-1/2} ∑ b_n²`. The jump of `φ_e` at `v = 1`
contributes the sinc kernel, which is controlled by Montgomery–Vaughan near resonance; the smooth
remainder decays like `1/f²`. -/
theorem abs_integral_criticalEndpointWeight_dilate_le {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M)
    (hS : DyadicScaleBlock S M) (b : ℕ → ℝ) {r : ℕ} (hr : 1 ≤ r) :
    |∫ v in Ioi 1, criticalEndpointWeight v * (realPhaseCombination S b v * realPhaseCombination S b (r * v))| ≤
      4 / Real.pi ^ 4 * (criticalEndpointDilationConstant / Real.sqrt r) * ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun n _ => sq_nonneg _
  obtain ⟨hm, hmsum⟩ := summable_endpointMajorant_and_tsum
  have h := abs_integral_weight_realPhaseCombination_dilate_le_of_bilinear
    integrableOn_criticalEndpointWeight S b r (μ := fun p => 1 / Real.sqrt r * E * endpointMajorant p)
    (hm.mul_left (1 / Real.sqrt r * E)) (fun p => by have := endpointMajorant_nonneg p; positivity)
    fun p hk hl => endpoint_harmonic_le hM hS b hr p hk hl
  refine h.trans (le_of_eq ?_)
  rw [tsum_mul_left, hmsum]
  ring

/-! ### The `ℓ²`-uniform critical prime channel -/

private theorem abs_realPhaseCombination_le (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    |realPhaseCombination S b v| ≤ 2 * ∑ n ∈ S, |b n| := by
  unfold realPhaseCombination
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [abs_mul]
  nlinarith [abs_factorialPhaseProfile_le (n + 1) v, abs_nonneg (b n)]

/-- **Collar–endpoint splitting of a critical correlation.** For `r ≥ 1`,
`∫ g_b(x) g_b(x - log r) dx = r^{-1/2} (∫_{v>1} ψ B_b(v)B_b(rv) + ∫_{v>1} φ_e B_b(v)B_b(rv))`. -/
theorem integral_criticalFactorialSource_mul_dilate_eq (S : Finset ℕ) (b : ℕ → ℝ) {r : ℕ} (hr : 1 ≤ r) :
    ∫ x, criticalFactorialSource S b x * criticalFactorialSource S b (x - Real.log r) =
      1 / Real.sqrt r * ((∫ v in Ioi 1, criticalCollarWeight v *
          (realPhaseCombination S b v * realPhaseCombination S b (r * v))) +
        ∫ v in Ioi 1, criticalEndpointWeight v *
          (realPhaseCombination S b v * realPhaseCombination S b (r * v))) := by
  set R := realPhaseCombination S b
  have hRc : Continuous fun v => R v * R (r * v) := by
    have : Continuous R := by
      have h := continuous_factorialPhaseCombination S (fun n => (b n : ℂ))
      exact (Complex.continuous_re.comp h).congr fun v => factorialPhaseCombination_re_eq S b v
    exact this.mul (this.comp (continuous_const.mul continuous_id))
  have hRb : ∀ v, ‖R v * R (r * v)‖ ≤ (2 * ∑ n ∈ S, |b n|) * (2 * ∑ n ∈ S, |b n|) := fun v => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_realPhaseCombination_le S b v) (abs_realPhaseCombination_le S b _)
      (abs_nonneg _) (by positivity)
  have h1 : IntegrableOn (fun v => criticalCollarWeight v * (R v * R (r * v))) (Ioi 1) :=
    integrableOn_criticalCollarWeight.mul_bdd hRc.aestronglyMeasurable (Eventually.of_forall hRb)
  have h2 : IntegrableOn (fun v => criticalEndpointWeight v * (R v * R (r * v))) (Ioi 1) :=
    integrableOn_criticalEndpointWeight.mul_bdd hRc.aestronglyMeasurable (Eventually.of_forall hRb)
  rw [criticalFactorialSource_correlation_eq S b (r := (r : ℝ)) (by exact_mod_cast hr), one_div,
    ← integral_add h1 h2]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv0 : 0 < v := lt_trans one_pos hv
  simp only [factorialPhaseCombination_re_eq, R]
  rw [← add_mul, criticalCollarWeight_add_criticalEndpointWeight hv0]
  ring

/-- The full critical prime constant `(4/π⁴)(K_c + K_e) ∑ Λ(r) r^{-3/2}`. -/
def criticalPrimeChannelConstant : ℝ :=
  4 / Real.pi ^ 4 * (dyadicDilationConstant criticalCollarMass criticalCollarCurvature +
    criticalEndpointDilationConstant) * ∑' r : ℕ, envelopePrimeMajorant 1 r

private theorem abs_criticalPrimeAtom_le_of_dyadic {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M)
    (hS : DyadicScaleBlock S M) (b : ℕ → ℝ) (r : ℕ) :
    |criticalPrimeAtom S b r| ≤ 4 / Real.pi ^ 4 * (dyadicDilationConstant criticalCollarMass
      criticalCollarCurvature + criticalEndpointDilationConstant) * (∑ n ∈ S, b n ^ 2) *
        envelopePrimeMajorant 1 r := by
  unfold criticalPrimeAtom envelopePrimeMajorant
  split_ifs with hr
  · have hr0 : (0 : ℝ) < r := by positivity
    have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
    have hc := abs_integral_weight_realPhaseCombination_dilate_le integrableOn_criticalCollarWeight
      abs_weightCosineTransform_criticalCollarWeight_le
      (fun f hf => abs_weightCosineTransform_criticalCollarWeight_le_div_sq hf)
      criticalCollarCurvature_nonneg hM hS b (r := r) (by omega)
    have he := abs_integral_criticalEndpointWeight_dilate_le hM hS b (r := r) (by omega)
    rw [integral_criticalFactorialSource_mul_dilate_eq S b (by omega), abs_mul, abs_mul,
      abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hs.le),
      abs_of_pos (by positivity : 0 < 1 / Real.sqrt r)]
    have hpow : (r : ℝ) ^ ((1 : ℝ) + 1 / 2) = Real.sqrt r * Real.sqrt r * Real.sqrt r := by
      rw [Real.rpow_add hr0, Real.rpow_one, ← Real.sqrt_eq_rpow, Real.mul_self_sqrt hr0.le]
    rw [hpow]
    have hΛ := (ArithmeticFunction.vonMangoldt_nonneg (n := r))
    calc (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r * (1 / Real.sqrt r * |_ + _|)
        ≤ (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r * (1 / Real.sqrt r *
          (4 / Real.pi ^ 4 * (dyadicDilationConstant criticalCollarMass criticalCollarCurvature /
            Real.sqrt r) * ∑ n ∈ S, b n ^ 2 +
           4 / Real.pi ^ 4 * (criticalEndpointDilationConstant / Real.sqrt r) * ∑ n ∈ S, b n ^ 2)) := by
          gcongr
          exact (abs_add_le _ _).trans (add_le_add hc he)
      _ = _ := by field_simp
  · simp

/-- **The critical prime channel is bounded on `ℓ²`.** On every dyadic scale block
`M ≤ n + 1 ≤ 2M` and for every real coefficient vector,
`|∑_r Λ(r) r^{-1/2} ac(log r)| ≤ C_P ∑ b_n²` with an absolute constant `C_P`, uniformly in the scale
and in the number and positions of the atoms. -/
theorem abs_criticalPrimeEnergy_le_of_dyadic {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M)
    (hS : DyadicScaleBlock S M) (b : ℕ → ℝ) :
    |criticalPrimeEnergy S b| ≤ criticalPrimeChannelConstant * ∑ n ∈ S, b n ^ 2 := by
  set C := 4 / Real.pi ^ 4 * (dyadicDilationConstant criticalCollarMass criticalCollarCurvature +
    criticalEndpointDilationConstant) * ∑ n ∈ S, b n ^ 2
  have hsum : Summable (envelopePrimeMajorant 1) :=
    summable_envelopePrimeMajorant_of_half_lt (by norm_num)
  have hbd := abs_criticalPrimeAtom_le_of_dyadic hM hS b
  have habs : Summable fun r => ‖criticalPrimeAtom S b r‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun r => by rw [Real.norm_eq_abs]; exact hbd r)
      (hsum.mul_left C)
  unfold criticalPrimeEnergy
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm habs).trans ?_
  refine (habs.tsum_le_tsum (fun r => by rw [Real.norm_eq_abs]; exact hbd r) (hsum.mul_left C)).trans
    (le_of_eq ?_)
  rw [tsum_mul_left]
  unfold criticalPrimeChannelConstant
  ring

end GaloisForLFunctions.ArithmeticPositivityTheory
