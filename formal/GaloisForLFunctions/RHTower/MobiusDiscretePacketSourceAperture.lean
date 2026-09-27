import GaloisForLFunctions.RHTower.MobiusDiscretePacketCriticalHorizon

/-!
# Source-index aperture of the cubic Möbius packets and the critical wedge

Fix `0 < A ≤ 4`, put `L_k = ⌊A k / log k⌋`, `a_δ = (5+δ)/(4+2δ)`, `U_k = ⌈k^{a_δ}⌉` and let the
middle packet be `c_k^mid = Σ_{L_k < n ≤ min(N, U_k)} μ(n) g_k(n)` for `k ≥ k_A` (and `c_k` below).
Then, for a threshold `k_A` and a constant `C_A` independent of `N` and `0 ≤ δ ≤ 1`,

`Σ_k C(4+δ+k, k) (c_k - c_k^mid)² ≤ C_A`.

The low source edge is split at `H = ⌊L_k/2⌋`: below `H` the telescoping absolute bound gives
`≪ k^{-4/3} (log k)^4`; on `(H, L_k]` the kernel is nondecreasing and summation by parts against
the Mertens bound `|M(x)| ≪ x E(x)` gives `≪ E(k)² (log k)^7 / k`.  Above `U_k` the kernel has
increments `≤ 8 x^{-4-δ}`, and summation by parts gives `w_k |c_k^high|² ≪ E(k)²/k`, the exponent
`a_δ` being exactly the one with `2 a_δ (2+δ) = 5+δ`.  All three are dominated by the summable
`(log k)^8 E(k)² / k`.

With `A = 4` and the critical horizon `K(N)`, a bounded full cubic energy along a set of cutoffs is
equivalent to a bounded **wedge energy** `Σ_{k_4 ≤ k < K(N)} w_k (c_k^mid)²`, and bounded wedge
returns on shifts cofinal at zero imply RH.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHTower.DiscretePacket

open CubicGamma MobiusRenewalPacketEnergy MobiusPacketDifference

/-- Lower source aperture `L_A(k) = ⌊A k / log k⌋`. -/
def lowerAperture (A : ℝ) (k : ℕ) : ℕ := ⌊A * k / Real.log k⌋₊

/-- The critical high-index exponent `a_δ = (5+δ)/(4+2δ)`. -/
def upperExponent (δ : ℝ) : ℝ := (5 + δ) / (4 + 2 * δ)

/-- Upper source aperture `U_δ(k) = ⌈k^{a_δ}⌉`. -/
def upperAperture (δ : ℝ) (k : ℕ) : ℕ := ⌈(k : ℝ) ^ upperExponent δ⌉₊

/-- The packet restricted to the source window `L_A(k) < n ≤ min(N, U_δ(k))`. -/
def wedgePacket (A δ : ℝ) (N k : ℕ) : ℝ :=
  ∑ n ∈ Ioc (lowerAperture A k) (min N (upperAperture δ k)), ((μ n : ℤ) : ℝ) * packetKernel δ k n

/-- The middle packet: the full packet below the threshold `k₀`, the window packet above. -/
def middlePacket (A δ : ℝ) (k₀ N k : ℕ) : ℝ :=
  if k < k₀ then cubicPacket δ N k else wedgePacket A δ N k

theorem one_le_upperExponent {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : 1 ≤ upperExponent δ := by
  unfold upperExponent
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem upperExponent_mul {δ : ℝ} (hδ0 : 0 ≤ δ) : 2 * upperExponent δ * (2 + δ) = 5 + δ := by
  unfold upperExponent
  field_simp
  ring

/-! ### Decomposition of the packet by source index -/

theorem sum_Ioc_min_eq {f : ℕ → ℝ} {L U N : ℕ} (hLU : L ≤ U) :
    ∑ n ∈ Ioc (min N L) (min N U), f n = ∑ n ∈ Ioc L (min N U), f n := by
  rcases le_total L N with h | h
  · rw [min_eq_right h]
  · have h1 : min N L = N := min_eq_left h
    have h2 : min N U = N := min_eq_left (h.trans hLU)
    rw [h1, h2, Finset.Ioc_self, Finset.Ioc_eq_empty (by omega)]

/-- `c_k - Σ_{L < n ≤ min(N,U)} = Σ_{n ≤ min(N,H)} + Σ_{min(N,H) < n ≤ min(N,L)} + Σ_{min(N,U) < n ≤ N}`. -/
theorem cubicPacket_sub_window_eq (δ : ℝ) (N k : ℕ) {H L U : ℕ} (hHL : H ≤ L) (hLU : L ≤ U) :
    cubicPacket δ N k - ∑ n ∈ Ioc L (min N U), ((μ n : ℤ) : ℝ) * packetKernel δ k n =
      ∑ n ∈ Ioc 0 (min N H), ((μ n : ℤ) : ℝ) * packetKernel δ k n +
        ∑ n ∈ Ioc (min N H) (min N L), ((μ n : ℤ) : ℝ) * packetKernel δ k n +
          ∑ n ∈ Ioc (min N U) N, ((μ n : ℤ) : ℝ) * packetKernel δ k n := by
  set f : ℕ → ℝ := fun n => ((μ n : ℤ) : ℝ) * packetKernel δ k n with hf
  have h1 : min N H ≤ min N L := min_le_min_left N hHL
  have h2 : min N L ≤ min N U := min_le_min_left N hLU
  have h3 : min N U ≤ N := min_le_left N U
  unfold cubicPacket
  rw [← sum_Ioc_min_eq (f := f) hLU,
    ← Finset.sum_Ioc_consecutive f (Nat.zero_le _) (h1.trans (h2.trans h3)),
    ← Finset.sum_Ioc_consecutive f h1 (h2.trans h3), ← Finset.sum_Ioc_consecutive f h2 h3]
  ring

/-! ### The three edge bounds -/

/-- The kernel is nondecreasing on `[a, b]` when `2 ≤ a` and `2b ≤ k`. -/
theorem packetKernel_nat_mono {δ : ℝ} (hδ1 : δ ≤ 1) {k a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hb : 2 * b ≤ k) : packetKernel δ k a ≤ packetKernel δ k b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    exact (ih (by omega)).trans (packetKernel_nat_le_succ hδ1 (by omega) (by omega))

/-- **Upper half of the low edge.**  Summation by parts on `(⌊L/2⌋, L]`. -/
theorem abs_sum_lowmid_le :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ N k L : ℕ, 2 ≤ L → 2 * L ≤ k →
      |∑ n ∈ Ioc (min N (L / 2)) (min N L), ((μ n : ℤ) : ℝ) * packetKernel δ k n| ≤
        C * mertensSaving L * ((L : ℝ) + 1) ^ (-(2 + δ)) *
          Real.exp (-(2 * k / ((L : ℝ) + 1))) := by
  obtain ⟨CW, hCW, hwin⟩ := exists_abs_abelMertens_window
  refine ⟨2 * CW, by positivity, fun δ hδ0 hδ1 N k L hL hLk => ?_⟩
  have hL1 : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  have hrhs : 0 ≤ 2 * CW * mertensSaving L * ((L : ℝ) + 1) ^ (-(2 + δ)) *
      Real.exp (-(2 * k / ((L : ℝ) + 1))) := by
    have := mertensSaving_pos (L : ℝ)
    positivity
  rcases le_or_gt N (L / 2) with hN | hN
  · rw [min_eq_left hN, min_eq_left (hN.trans (Nat.div_le_self L 2)), Finset.Ioc_self,
      Finset.sum_empty, abs_zero]
    exact hrhs
  set H : ℕ := L / 2 with hH
  have hH1 : 1 ≤ H := by omega
  have hHL : H < L := by omega
  have hminH : min N H = H := min_eq_right hN.le
  rw [hminH]
  set b : ℕ := min N L with hb
  have hHb : H < b := lt_min hN hHL
  have hbL : b ≤ L := min_le_right N L
  have h := abs_sum_Ioc_moebius_mul_le_of_monotone (fun n => packetKernel δ k n) hHb
    (B := CW * L * mertensSaving L)
    (fun n hn1 hn2 => hwin n L (by omega) (hn2.trans hbL) (by omega))
    (packetKernel_nonneg k (by push_cast; linarith [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)]))
    (fun n hn1 hn2 => packetKernel_nat_le_succ hδ1 (by omega) (by omega))
  refine h.trans ?_
  have hgb : packetKernel δ k b ≤ packetKernel δ k L :=
    packetKernel_nat_mono hδ1 (by omega) hbL hLk
  have hgL := packetKernel_le (δ := δ) k (show (1 : ℝ) ≤ L by exact_mod_cast (by omega : 1 ≤ L))
  have hLX : (L : ℝ) * ((L : ℝ) + 1) ^ (-(3 + δ)) ≤ ((L : ℝ) + 1) ^ (-(2 + δ)) := by
    have e : ((L : ℝ) + 1) ^ (-(2 + δ)) = ((L : ℝ) + 1) * ((L : ℝ) + 1) ^ (-(3 + δ)) := by
      rw [show -(2 + δ) = 1 + -(3 + δ) by ring, Real.rpow_add hL1, Real.rpow_one]
    rw [e]
    gcongr
    linarith
  have hE := mertensSaving_pos (L : ℝ)
  have hB0 : 0 ≤ 2 * (CW * L * mertensSaving L) := by positivity
  calc 2 * (CW * L * mertensSaving L) * packetKernel δ k b
      ≤ 2 * (CW * L * mertensSaving L) *
          (((L : ℝ) + 1) ^ (-(3 + δ)) * Real.exp (-(2 * k / ((L : ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left (hgb.trans hgL) hB0
    _ = 2 * CW * mertensSaving L * ((L : ℝ) * ((L : ℝ) + 1) ^ (-(3 + δ))) *
          Real.exp (-(2 * k / ((L : ℝ) + 1))) := by ring
    _ ≤ _ := by gcongr

/-- **High edge.**  For `1 ≤ k ≤ U`, `|Σ_{min(N,U) < n ≤ N} μ(n) g_k(n)| ≤ C E(U) U^{-2-δ}`. -/
theorem abs_sum_high_le :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ N k U : ℕ, 1 ≤ k → k ≤ U →
      |∑ n ∈ Ioc (min N U) N, ((μ n : ℤ) : ℝ) * packetKernel δ k n| ≤
        C * mertensSaving U * (U : ℝ) ^ (-(2 + δ)) := by
  obtain ⟨CM, hCM, hM⟩ := exists_abs_abelMertens_le_all
  refine ⟨6 * CM, by positivity, fun δ hδ0 hδ1 N k U hk hkU => ?_⟩
  have hU1 : 1 ≤ U := hk.trans hkU
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU1
  have hEU := mertensSaving_pos (U : ℝ)
  have hrhs : 0 ≤ 6 * CM * mertensSaving U * (U : ℝ) ^ (-(2 + δ)) := by
    have := Real.rpow_pos_of_pos hU0 (-(2 + δ))
    positivity
  rcases le_or_gt N U with hN | hN
  · rw [min_eq_left hN, Finset.Ioc_self, Finset.sum_empty, abs_zero]
    exact hrhs
  rw [min_eq_right hN.le]
  -- `|M(n)| ≤ C n E(U)` beyond `U`
  have hMU : ∀ n : ℕ, U ≤ n → |abelMertens n| ≤ CM * n * mertensSaving U := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ U := by exact_mod_cast hU1
    have hnU : (U : ℝ) ≤ n := by exact_mod_cast hn
    have hE := mertensSaving_antitone hn1 hnU
    refine (hM n).trans ?_
    gcongr
  -- the kernel below `x^{-3-δ}`
  have hg : ∀ n : ℕ, 1 ≤ n → |packetKernel δ k n| ≤ (n : ℝ) ^ (-(3 + δ)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_of_nonneg (packetKernel_nonneg k hn1)]
    refine (packetKernel_le k hn1).trans ?_
    calc ((n : ℝ) + 1) ^ (-(3 + δ)) * Real.exp (-(2 * k / ((n : ℝ) + 1)))
        ≤ ((n : ℝ) + 1) ^ (-(3 + δ)) * 1 := by
          gcongr
          rw [Real.exp_le_one_iff, neg_nonpos]
          positivity
      _ ≤ _ := by
          rw [mul_one]
          exact rpow_neg_le_of_le (by linarith) (by linarith) (by linarith)
  have hsplit (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) * (n : ℝ) ^ (-(3 + δ)) = (n : ℝ) ^ (-(2 + δ)) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [show -(2 + δ) = 1 + -(3 + δ) by ring, Real.rpow_add hn0, Real.rpow_one]
  have hUmono : ∀ n : ℕ, U ≤ n → (n : ℝ) ^ (-(2 + δ)) ≤ (U : ℝ) ^ (-(2 + δ)) := fun n hn =>
    rpow_neg_le_of_le hU0 (by exact_mod_cast hn) (by linarith)
  have hab := abs_sum_Ioc_moebius_mul_le (fun n => packetKernel δ k n) hN
  refine hab.trans ?_
  -- the two boundary terms
  have hb1 : |packetKernel δ k N| * |abelMertens N| ≤ CM * mertensSaving U * (U : ℝ) ^ (-(2 + δ)) := by
    have hN1 : 1 ≤ N := by omega
    calc |packetKernel δ k N| * |abelMertens N| ≤ (N : ℝ) ^ (-(3 + δ)) * (CM * N * mertensSaving U) :=
          mul_le_mul (hg N hN1) (hMU N hN.le) (abs_nonneg _) (by positivity)
      _ = CM * mertensSaving U * ((N : ℝ) * (N : ℝ) ^ (-(3 + δ))) := by ring
      _ ≤ _ := by
          rw [hsplit N hN1]
          exact mul_le_mul_of_nonneg_left (hUmono N hN.le) (by positivity)
  have hb2 : |packetKernel δ k ((U + 1 : ℕ) : ℝ)| * |abelMertens U| ≤
      CM * mertensSaving U * (U : ℝ) ^ (-(2 + δ)) := by
    have hg' : |packetKernel δ k ((U + 1 : ℕ) : ℝ)| ≤ (U : ℝ) ^ (-(3 + δ)) :=
      (hg (U + 1) (by omega)).trans (rpow_neg_le_of_le hU0 (by push_cast; linarith) (by linarith))
    calc |packetKernel δ k ((U + 1 : ℕ) : ℝ)| * |abelMertens U|
        ≤ (U : ℝ) ^ (-(3 + δ)) * (CM * U * mertensSaving U) :=
          mul_le_mul hg' (hMU U le_rfl) (abs_nonneg _) (by positivity)
      _ = CM * mertensSaving U * ((U : ℝ) * (U : ℝ) ^ (-(3 + δ))) := by ring
      _ = _ := by rw [hsplit U hU1]
  -- the variation
  have hvar : ∑ n ∈ Ioc U (N - 1), |packetKernel δ k ((n + 1 : ℕ) : ℝ) - packetKernel δ k n| *
      |abelMertens n| ≤ 4 * CM * mertensSaving U * (U : ℝ) ^ (-(2 + δ)) := by
    have hterm : ∀ n ∈ Ioc U (N - 1), |packetKernel δ k ((n + 1 : ℕ) : ℝ) - packetKernel δ k n| *
        |abelMertens n| ≤ 8 * CM * mertensSaving U * (n : ℝ) ^ (-((2 + δ) + 1)) := by
      intro n hn
      have hn' := mem_Ioc.mp hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have hkn : (k : ℝ) ≤ n := by exact_mod_cast (by omega : k ≤ n)
      have hd := abs_packetKernel_succ_sub_le hδ0 hδ1 hn1 hkn
      push_cast
      have hn0 : (0 : ℝ) < n := by linarith
      have e : (n : ℝ) ^ (-(4 + δ)) * n = (n : ℝ) ^ (-((2 + δ) + 1)) := by
        rw [show -((2 + δ) + 1) = -(4 + δ) + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
      calc |packetKernel δ k ((n : ℝ) + 1) - packetKernel δ k n| * |abelMertens n|
          ≤ 8 * (n : ℝ) ^ (-(4 + δ)) * (CM * n * mertensSaving U) :=
            mul_le_mul hd (hMU n hn'.1.le) (abs_nonneg _) (by positivity)
        _ = 8 * CM * mertensSaving U * ((n : ℝ) ^ (-(4 + δ)) * n) := by ring
        _ = _ := by rw [e]
    have htail := sum_Ioc_rpow_neg_le (s := 2 + δ) (by linarith) hU1 (N - 1)
    calc _ ≤ ∑ n ∈ Ioc U (N - 1), 8 * CM * mertensSaving U * (n : ℝ) ^ (-((2 + δ) + 1)) :=
          sum_le_sum hterm
      _ = 8 * CM * mertensSaving U * ∑ n ∈ Ioc U (N - 1), (n : ℝ) ^ (-((2 + δ) + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ 8 * CM * mertensSaving U * ((U : ℝ) ^ (-(2 + δ)) / (2 + δ)) := by gcongr
      _ ≤ 8 * CM * mertensSaving U * ((U : ℝ) ^ (-(2 + δ)) / 2) := by
          gcongr
          linarith
      _ = _ := by ring
  have hcast : ∀ n : ℕ, packetKernel δ k ((n + 1 : ℕ) : ℝ) = packetKernel δ k ((n : ℝ) + 1) := by
    intro n; push_cast; rfl
  simp only [hcast] at hb2 hvar ⊢
  linarith

/-! ### The weighted edge bounds -/

/-- `y^p ≤ (1 + y)^q` for `0 ≤ y`, `0 ≤ p ≤ q` (`q` a natural number). -/
theorem rpow_le_one_add_pow {y p : ℝ} (hy : 0 ≤ y) (hp : 0 ≤ p) {q : ℕ} (hpq : p ≤ q) :
    y ^ p ≤ (1 + y) ^ q := by
  calc y ^ p ≤ (1 + y) ^ p := Real.rpow_le_rpow hy (by linarith) hp
    _ ≤ (1 + y) ^ (q : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hpq
    _ = (1 + y) ^ q := Real.rpow_natCast _ _

/-- `k^p R^{-p-δ} ≤ (1 + k/R)^q` for `R ≥ 1`. -/
theorem rpow_mul_rpow_neg_le {k R p δ : ℝ} (hk : 0 < k) (hR : 1 ≤ R) (hp : 0 ≤ p) (hδ : 0 ≤ δ)
    {q : ℕ} (hpq : p ≤ q) : k ^ p * R ^ (-(p + δ)) ≤ (1 + k / R) ^ q := by
  have hR0 : 0 < R := by linarith
  have e : k ^ p * R ^ (-(p + δ)) = (k / R) ^ p * R ^ (-δ) := by
    rw [Real.div_rpow hk.le hR0.le, show -(p + δ) = -p + -δ by ring, Real.rpow_add hR0,
      Real.rpow_neg hR0.le p]
    field_simp
  rw [e]
  have h1 : R ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
  have h2 := rpow_le_one_add_pow (y := k / R) (by positivity) hp hpq
  have h3 : 0 ≤ (k / R) ^ p := Real.rpow_nonneg (by positivity) _
  calc (k / R) ^ p * R ^ (-δ) ≤ (1 + k / R) ^ q * 1 := mul_le_mul h2 h1 (by positivity) (by positivity)
    _ = _ := mul_one _

/-- Weighted square of the lower half of the low edge: `≤ e^5 (1 + k/R)^3 k^{-4/3}` when
`R ≤ 3k/log k`. -/
theorem weighted_lowlow_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {k R : ℝ} (hk : 1 ≤ k)
    (hR : 1 ≤ R) (hRk : R * Real.log k ≤ 3 * k) :
    Real.exp 5 * k ^ (4 + δ) *
        (R ^ (-(1 + δ)) * Real.exp (-(2 * k / R)) / k) ^ 2 ≤
      Real.exp 5 * (1 + k / R) ^ 3 * k ^ (-(4 / 3 : ℝ)) := by
  have hk0 : 0 < k := by linarith
  have hR0 : 0 < R := by linarith
  have hexp : Real.exp (-(2 * k / R)) ^ 2 ≤ k ^ (-(4 / 3 : ℝ)) := by
    rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hk0]
    apply Real.exp_le_exp.mpr
    have : 4 / 3 * Real.log k ≤ 4 * k / R := by
      rw [le_div_iff₀ hR0]
      nlinarith
    push_cast
    have e : (2 : ℝ) * -(2 * k / R) = -(4 * k / R) := by ring
    rw [e]
    linarith
  have hpow : k ^ (4 + δ) * (R ^ (-(1 + δ))) ^ 2 / k ^ 2 = k ^ (2 + δ) * R ^ (-((2 + δ) + δ)) := by
    rw [← Real.rpow_natCast (R ^ (-(1 + δ))), ← Real.rpow_mul hR0.le,
      show (4 : ℝ) + δ = (2 + δ) + ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_add hk0,
      Real.rpow_natCast]
    have : k ^ 2 ≠ 0 := by positivity
    field_simp
    congr 2
    push_cast
    ring
  have hbase := rpow_mul_rpow_neg_le (q := 3) hk0 hR (by linarith : (0 : ℝ) ≤ 2 + δ) hδ0
    (by push_cast; linarith)
  calc Real.exp 5 * k ^ (4 + δ) * (R ^ (-(1 + δ)) * Real.exp (-(2 * k / R)) / k) ^ 2
      = Real.exp 5 * (k ^ (4 + δ) * (R ^ (-(1 + δ))) ^ 2 / k ^ 2) *
          Real.exp (-(2 * k / R)) ^ 2 := by
        field_simp
    _ = Real.exp 5 * (k ^ (2 + δ) * R ^ (-((2 + δ) + δ))) * Real.exp (-(2 * k / R)) ^ 2 := by
        rw [hpow]
    _ ≤ Real.exp 5 * (1 + k / R) ^ 3 * k ^ (-(4 / 3 : ℝ)) := by
        gcongr

/-- Weighted square of the upper half of the low edge. -/
theorem weighted_lowmid_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {k R C E : ℝ} (hk : 1 ≤ k)
    (hR : 1 ≤ R) (hRk : R * Real.log k ≤ 4 * k + Real.log k) (hlog : Real.log k ^ 2 ≤ 4 * k) :
    Real.exp 5 * k ^ (4 + δ) *
        (C * E * R ^ (-(2 + δ)) * Real.exp (-(2 * k / R))) ^ 2 ≤
      Real.exp 6 * C ^ 2 * E ^ 2 * (1 + k / R) ^ 5 / k := by
  have hk0 : 0 < k := by linarith
  have hR0 : 0 < R := by linarith
  have hl0 : 0 ≤ Real.log k := Real.log_nonneg hk
  -- `e^{-4k/R} ≤ e/k`
  have hexp : Real.exp (-(2 * k / R)) ^ 2 ≤ Real.exp 1 / k := by
    rw [← Real.exp_nat_mul, show Real.exp 1 / k = Real.exp (1 - Real.log k) by
      rw [Real.exp_sub, Real.exp_log hk0]]
    apply Real.exp_le_exp.mpr
    have h : Real.log k - 1 ≤ 4 * k / R := by
      rw [le_div_iff₀ hR0]
      nlinarith
    push_cast
    have e : (2 : ℝ) * -(2 * k / R) = -(4 * k / R) := by ring
    rw [e]
    linarith
  have hpow : k ^ (4 + δ) * (R ^ (-(2 + δ))) ^ 2 = k ^ (4 + δ) * R ^ (-((4 + δ) + δ)) := by
    rw [← Real.rpow_natCast (R ^ (-(2 + δ))), ← Real.rpow_mul hR0.le]
    congr 2
    push_cast
    ring
  have hbase := rpow_mul_rpow_neg_le (q := 5) hk0 hR (by linarith : (0 : ℝ) ≤ 4 + δ) hδ0
    (by push_cast; linarith)
  have he : Real.exp 5 * Real.exp 1 = Real.exp 6 := by rw [← Real.exp_add]; norm_num
  calc Real.exp 5 * k ^ (4 + δ) * (C * E * R ^ (-(2 + δ)) * Real.exp (-(2 * k / R))) ^ 2
      = Real.exp 5 * C ^ 2 * E ^ 2 * (k ^ (4 + δ) * (R ^ (-(2 + δ))) ^ 2) *
          Real.exp (-(2 * k / R)) ^ 2 := by ring
    _ = Real.exp 5 * C ^ 2 * E ^ 2 * (k ^ (4 + δ) * R ^ (-((4 + δ) + δ))) *
          Real.exp (-(2 * k / R)) ^ 2 := by rw [hpow]
    _ ≤ Real.exp 5 * C ^ 2 * E ^ 2 * (1 + k / R) ^ 5 * (Real.exp 1 / k) := by gcongr
    _ = _ := by rw [← he]; ring

/-- Weighted square of the high edge: `≤ e^5 C² E(k)² / k` at the critical exponent. -/
theorem weighted_high_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {k : ℕ} (hk : 1 ≤ k) (C : ℝ) :
    Real.exp 5 * (k : ℝ) ^ (4 + δ) *
        (C * mertensSaving (upperAperture δ k) *
          ((upperAperture δ k : ℕ) : ℝ) ^ (-(2 + δ))) ^ 2 ≤
      Real.exp 5 * C ^ 2 * mertensSaving k ^ 2 / k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have ha := one_le_upperExponent hδ0 hδ1
  have hkU : (k : ℝ) ^ upperExponent δ ≤ (upperAperture δ k : ℝ) := Nat.le_ceil _
  have hka : (k : ℝ) ≤ (k : ℝ) ^ upperExponent δ := Real.self_le_rpow_of_one_le hk1 ha
  have hE : mertensSaving (upperAperture δ k) ≤ mertensSaving k :=
    mertensSaving_antitone hk1 (hka.trans hkU)
  have hkapos : 0 < (k : ℝ) ^ upperExponent δ := Real.rpow_pos_of_pos hk0 _
  have hU : ((upperAperture δ k : ℕ) : ℝ) ^ (-(2 + δ)) ≤ ((k : ℝ) ^ upperExponent δ) ^ (-(2 + δ)) :=
    rpow_neg_le_of_le hkapos hkU (by linarith)
  have hcrit : (k : ℝ) ^ (4 + δ) * (((k : ℝ) ^ upperExponent δ) ^ (-(2 + δ))) ^ 2 = 1 / k := by
    rw [← Real.rpow_mul hk0.le, ← Real.rpow_natCast, ← Real.rpow_mul hk0.le, ← Real.rpow_add hk0]
    have hm := upperExponent_mul hδ0
    have e : (4 + δ) + upperExponent δ * -(2 + δ) * ((2 : ℕ) : ℝ) = -1 := by
      push_cast
      linarith
    rw [e, Real.rpow_neg_one, one_div]
  have hE0 := mertensSaving_pos ((upperAperture δ k : ℕ) : ℝ)
  have hU0 : 0 ≤ ((upperAperture δ k : ℕ) : ℝ) ^ (-(2 + δ)) := Real.rpow_nonneg (by positivity) _
  calc Real.exp 5 * (k : ℝ) ^ (4 + δ) *
        (C * mertensSaving (upperAperture δ k) * ((upperAperture δ k : ℕ) : ℝ) ^ (-(2 + δ))) ^ 2
      = Real.exp 5 * C ^ 2 * mertensSaving (upperAperture δ k) ^ 2 *
          ((k : ℝ) ^ (4 + δ) * (((upperAperture δ k : ℕ) : ℝ) ^ (-(2 + δ))) ^ 2) := by ring
    _ ≤ Real.exp 5 * C ^ 2 * mertensSaving k ^ 2 *
          ((k : ℝ) ^ (4 + δ) * (((k : ℝ) ^ upperExponent δ) ^ (-(2 + δ))) ^ 2) := by
        gcongr
    _ = _ := by rw [hcrit]; ring

/-! ### The aperture geometry for large `k` -/

/-- For every `A > 0`, eventually `log k ≥ 24`, `8 log k ≤ A k` and `(log k)² ≤ 4k`. -/
theorem eventually_aperture_facts {A : ℝ} (hA0 : 0 < A) :
    ∃ k₁ : ℕ, ∀ k : ℕ, k₁ ≤ k →
      24 ≤ Real.log k ∧ 8 * Real.log k ≤ A * k ∧ Real.log k ^ 2 ≤ 4 * k := by
  have h1 : ∀ᶠ x : ℝ in atTop, 24 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 24)
  have h2 : ∀ᶠ x : ℝ in atTop, Real.log x ^ 1 / (1 * x + 0) ≤ A / 8 :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).eventually
      (eventually_le_nhds (by positivity))
  have h3 : ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 / (1 * x + 0) ≤ 4 :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).eventually
      (eventually_le_nhds (by norm_num))
  obtain ⟨X, hX⟩ := eventually_atTop.mp ((h1.and h2).and (h3.and (eventually_gt_atTop 0)))
  obtain ⟨k₁, hk₁⟩ := exists_nat_ge X
  refine ⟨k₁, fun k hk => ?_⟩
  obtain ⟨⟨ha, hb⟩, hc, hpos⟩ := hX k (hk₁.trans (by exact_mod_cast hk))
  simp only [pow_one, one_mul, add_zero] at hb hc
  refine ⟨ha, ?_, ?_⟩
  · rw [div_le_iff₀ hpos] at hb
    linarith
  · rw [div_le_iff₀ hpos] at hc
    linarith

/-- The source-index geometry of the aperture at large `k`. -/
theorem aperture_geometry {A : ℝ} (hA0 : 0 < A) (hA4 : A ≤ 4) {k : ℕ} (hℓ : 24 ≤ Real.log k)
    (hAk : 8 * Real.log k ≤ A * k) (hlog : Real.log k ^ 2 ≤ 4 * k) :
    2 ≤ lowerAperture A k ∧ 2 * lowerAperture A k ≤ k ∧
      6 * (((lowerAperture A k / 2 : ℕ) : ℝ) + 1) ≤ k ∧
      (((lowerAperture A k / 2 : ℕ) : ℝ) + 2) * Real.log k ≤ 3 * k ∧
      (k : ℝ) / (((lowerAperture A k / 2 : ℕ) : ℝ) + 2) ≤ 2 / A * Real.log k ∧
      ((lowerAperture A k : ℝ) + 1) * Real.log k ≤ 4 * k + Real.log k ∧
      (k : ℝ) / ((lowerAperture A k : ℝ) + 1) ≤ 1 / A * Real.log k ∧
      (k : ℝ) / (lowerAperture A k : ℝ) ≤ 2 / A * Real.log k := by
  set ℓ : ℝ := Real.log k with hℓdef
  have hℓ0 : 0 < ℓ := by linarith
  have hk0 : (0 : ℝ) < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [hℓdef, h] at hℓ; simp at hℓ; linarith
    · exact_mod_cast h
  set x : ℝ := A * k / ℓ with hx
  have hx8 : 8 ≤ x := by rw [hx, le_div_iff₀ hℓ0]; linarith
  have hxk : x ≤ k / 6 := by
    rw [hx, div_le_div_iff₀ hℓ0 (by norm_num)]
    nlinarith
  have hℓk : 2 * ℓ ≤ k := by nlinarith
  set L : ℕ := lowerAperture A k with hL
  have hLx : (L : ℝ) ≤ x := Nat.floor_le (by positivity)
  have hxL : x < (L : ℝ) + 1 := Nat.lt_floor_add_one x
  have hL2r : (2 : ℝ) ≤ L := by linarith
  have hL2 : 2 ≤ L := by exact_mod_cast hL2r
  set H : ℕ := L / 2 with hH
  have hH1 : 2 * H ≤ L := Nat.mul_div_le L 2
  have hH2 : L ≤ 2 * H + 1 := by omega
  have hH1r : 2 * (H : ℝ) ≤ L := by exact_mod_cast hH1
  have hH2r : (L : ℝ) ≤ 2 * H + 1 := by exact_mod_cast hH2
  have hxA : A * k = x * ℓ := by rw [hx]; field_simp
  refine ⟨hL2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (2 * L : ℝ) ≤ k := by linarith
    exact_mod_cast this
  · linarith
  · nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have : x / 2 ≤ (H : ℝ) + 2 := by linarith
    calc (k : ℝ) = 2 / A * ℓ * (x / 2) := by rw [hx]; field_simp
      _ ≤ 2 / A * ℓ * ((H : ℝ) + 2) := by gcongr
  · nlinarith
  · rw [div_le_iff₀ (by positivity)]
    calc (k : ℝ) = 1 / A * ℓ * x := by rw [hx]; field_simp
      _ ≤ 1 / A * ℓ * ((L : ℝ) + 1) := by gcongr
  · rw [div_le_iff₀ (by linarith)]
    have : x / 2 ≤ (L : ℝ) := by linarith
    calc (k : ℝ) = 2 / A * ℓ * (x / 2) := by rw [hx]; field_simp
      _ ≤ 2 / A * ℓ * (L : ℝ) := by gcongr

/-! ### The aperture error bound (7) -/

theorem add_add_sq_le_three (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

theorem aperture_majorant_nonneg (k : ℕ) : 0 ≤ Real.log k ^ 8 * mertensSaving k ^ 2 / k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
    positivity

/-- **Pointwise aperture bound.**  Beyond a threshold, uniformly in `N` and `0 ≤ δ ≤ 1`,
`w_k (c_k - c_k^mid)² ≤ C (log k)^8 E(k)² / k`. -/
theorem weighted_aperture_error_le {A : ℝ} (hA0 : 0 < A) (hA4 : A ≤ 4) :
    ∃ k₁ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ N k : ℕ, k₁ ≤ k →
      binomialWeight (5 + δ) k * (cubicPacket δ N k - wedgePacket A δ N k) ^ 2 ≤
        C * (Real.log k ^ 8 * mertensSaving k ^ 2 / k) := by
  obtain ⟨k₁, hk₁⟩ := eventually_aperture_facts hA0
  obtain ⟨CB, hCB, hmid⟩ := abs_sum_lowmid_le
  obtain ⟨CH, hCH, hhigh⟩ := abs_sum_high_le
  obtain ⟨CE, hCE, hthird⟩ := exists_rpow_neg_third_le_mertensSaving_sq
  obtain ⟨Ks, hKs, hslow⟩ := mertensSaving_slow (η := 1) one_pos
  set c₁ : ℝ := Real.exp 5 * (1 + 2 / A) ^ 3 * CE with hc₁
  set c₂ : ℝ := Real.exp 6 * CB ^ 2 * Ks ^ 2 * (2 / A) ^ 2 * (1 + 1 / A) ^ 5 with hc₂
  set c₃ : ℝ := Real.exp 5 * CH ^ 2 with hc₃
  refine ⟨k₁, 3 * (c₁ + c₂ + c₃), by positivity, fun δ hδ0 hδ1 N k hk => ?_⟩
  obtain ⟨hℓ24, hAk, hlog⟩ := hk₁ k hk
  obtain ⟨hL2, hLk, hH6, hHℓ, hkH, hLℓ, hkL1, hkL⟩ := aperture_geometry hA0 hA4 hℓ24 hAk hlog
  set ℓ : ℝ := Real.log k with hℓdef
  set L : ℕ := lowerAperture A k with hLdef
  set H : ℕ := L / 2 with hHdef
  set U : ℕ := upperAperture δ k with hUdef
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hk1 : 1 ≤ k := by
    have : (2 : ℝ) ≤ k := by
      have : (4 : ℝ) ≤ 2 * L := by exact_mod_cast (by omega : 4 ≤ 2 * L)
      have : (2 * L : ℝ) ≤ k := by exact_mod_cast hLk
      linarith
    exact_mod_cast (by linarith : (1 : ℝ) ≤ k)
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := by linarith
  have hkU : k ≤ U := by
    have h1 : (k : ℝ) ≤ (k : ℝ) ^ upperExponent δ :=
      Real.self_le_rpow_of_one_le hk1r (one_le_upperExponent hδ0 hδ1)
    have h2 : (k : ℝ) ^ upperExponent δ ≤ U := Nat.le_ceil _
    exact_mod_cast h1.trans h2
  have hLU : L ≤ U := by omega
  have hHL : H ≤ L := Nat.div_le_self L 2
  -- decomposition
  have hdec := cubicPacket_sub_window_eq δ N k hHL hLU
  have hwedge : wedgePacket A δ N k =
      ∑ n ∈ Ioc L (min N U), ((μ n : ℤ) : ℝ) * packetKernel δ k n := rfl
  rw [hwedge, hdec]
  set S₁ := ∑ n ∈ Ioc 0 (min N H), ((μ n : ℤ) : ℝ) * packetKernel δ k n with hS₁
  set S₂ := ∑ n ∈ Ioc (min N H) (min N L), ((μ n : ℤ) : ℝ) * packetKernel δ k n with hS₂
  set S₃ := ∑ n ∈ Ioc (min N U) N, ((μ n : ℤ) : ℝ) * packetKernel δ k n with hS₃
  -- the three bounds
  have hb₁ : |S₁| ≤ ((H : ℝ) + 2) ^ (-(1 + δ)) * Real.exp (-(2 * k / ((H : ℝ) + 2))) / k :=
    abs_sum_low_packetKernel_le hδ0 hδ1 hk1 (min_le_right N H) hH6
  have hb₂ : |S₂| ≤ CB * mertensSaving L * ((L : ℝ) + 1) ^ (-(2 + δ)) *
      Real.exp (-(2 * k / ((L : ℝ) + 1))) := hmid δ hδ0 hδ1 N k L hL2 hLk
  have hb₃ : |S₃| ≤ CH * mertensSaving U * (U : ℝ) ^ (-(2 + δ)) :=
    hhigh δ hδ0 hδ1 N k U hk1 hkU
  have hw := binomialWeight_le_rpow hδ0 hδ1 hk1
  have hw0 := binomialWeight_nonneg (show (0 : ℝ) ≤ 5 + δ by linarith) k
  -- weighted pieces
  have hH1 : (1 : ℝ) ≤ (H : ℝ) + 2 := by linarith [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)]
  have hL1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hq₁ : Real.exp 5 * (k : ℝ) ^ (4 + δ) *
      (((H : ℝ) + 2) ^ (-(1 + δ)) * Real.exp (-(2 * k / ((H : ℝ) + 2))) / k) ^ 2 ≤
        c₁ * (ℓ ^ 8 * mertensSaving k ^ 2 / k) := by
    refine (weighted_lowlow_le hδ0 hδ1 hk1r hH1 hHℓ).trans ?_
    have hy : 1 + (k : ℝ) / ((H : ℝ) + 2) ≤ (1 + 2 / A) * ℓ := by
      have e : (1 + 2 / A) * ℓ = ℓ + 2 / A * ℓ := by ring
      rw [e]
      linarith
    have hy0 : 0 ≤ 1 + (k : ℝ) / ((H : ℝ) + 2) := by positivity
    have hk43 : (k : ℝ) ^ (-(4 / 3 : ℝ)) = (k : ℝ) ^ (-(1 / 3 : ℝ)) / k := by
      rw [show -(4 / 3 : ℝ) = -(1 / 3) - 1 by norm_num, Real.rpow_sub_one hk0.ne']
    have hth := hthird k hk1r
    have hℓ38 : ℓ ^ 3 ≤ ℓ ^ 8 := pow_le_pow_right₀ hℓ1 (by norm_num)
    have hE0 := mertensSaving_pos (k : ℝ)
    calc Real.exp 5 * (1 + (k : ℝ) / ((H : ℝ) + 2)) ^ 3 * (k : ℝ) ^ (-(4 / 3 : ℝ))
        ≤ Real.exp 5 * ((1 + 2 / A) * ℓ) ^ 3 * ((CE * mertensSaving k ^ 2) / k) := by
          rw [hk43]
          gcongr
      _ = Real.exp 5 * (1 + 2 / A) ^ 3 * CE * (ℓ ^ 3 * mertensSaving k ^ 2 / k) := by ring
      _ ≤ Real.exp 5 * (1 + 2 / A) ^ 3 * CE * (ℓ ^ 8 * mertensSaving k ^ 2 / k) := by gcongr
  have hq₂ : Real.exp 5 * (k : ℝ) ^ (4 + δ) *
      (CB * mertensSaving L * ((L : ℝ) + 1) ^ (-(2 + δ)) *
        Real.exp (-(2 * k / ((L : ℝ) + 1)))) ^ 2 ≤ c₂ * (ℓ ^ 8 * mertensSaving k ^ 2 / k) := by
    refine (weighted_lowmid_le hδ0 hδ1 hk1r hL1 hLℓ hlog).trans ?_
    have hy : 1 + (k : ℝ) / ((L : ℝ) + 1) ≤ (1 + 1 / A) * ℓ := by
      have e : (1 + 1 / A) * ℓ = ℓ + 1 / A * ℓ := by ring
      rw [e]
      linarith
    have hy0 : 0 ≤ 1 + (k : ℝ) / ((L : ℝ) + 1) := by positivity
    have hLr : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    have hLk' : (L : ℝ) ≤ k := by
      have : (2 * L : ℝ) ≤ k := by exact_mod_cast hLk
      linarith
    have hEL : mertensSaving L ≤ Ks * mertensSaving k * (2 / A * ℓ) := by
      have h := hslow L k hLr hLk'
      rw [Real.rpow_one] at h
      have hE0 := mertensSaving_pos (k : ℝ)
      calc mertensSaving L ≤ Ks * mertensSaving k * ((k : ℝ) / L) := h
        _ ≤ Ks * mertensSaving k * (2 / A * ℓ) := by gcongr
    have hEL0 := mertensSaving_pos (L : ℝ)
    have hEL2 : mertensSaving L ^ 2 ≤ (Ks * mertensSaving k * (2 / A * ℓ)) ^ 2 :=
      pow_le_pow_left₀ hEL0.le hEL 2
    have hℓ78 : ℓ ^ 7 ≤ ℓ ^ 8 := pow_le_pow_right₀ hℓ1 (by norm_num)
    have hE0 := mertensSaving_pos (k : ℝ)
    calc Real.exp 6 * CB ^ 2 * mertensSaving L ^ 2 * (1 + (k : ℝ) / ((L : ℝ) + 1)) ^ 5 / k
        ≤ Real.exp 6 * CB ^ 2 * (Ks * mertensSaving k * (2 / A * ℓ)) ^ 2 *
            ((1 + 1 / A) * ℓ) ^ 5 / k := by gcongr
      _ = c₂ * (ℓ ^ 7 * mertensSaving k ^ 2 / k) := by rw [hc₂]; ring
      _ ≤ c₂ * (ℓ ^ 8 * mertensSaving k ^ 2 / k) := by gcongr
  have hq₃ : Real.exp 5 * (k : ℝ) ^ (4 + δ) *
      (CH * mertensSaving U * (U : ℝ) ^ (-(2 + δ))) ^ 2 ≤ c₃ * (ℓ ^ 8 * mertensSaving k ^ 2 / k) := by
    refine (weighted_high_le hδ0 hδ1 hk1 CH).trans ?_
    have hℓ8 : 1 ≤ ℓ ^ 8 := one_le_pow₀ hℓ1
    have hE0 := mertensSaving_pos (k : ℝ)
    calc Real.exp 5 * CH ^ 2 * mertensSaving k ^ 2 / k
        = c₃ * (1 * mertensSaving k ^ 2 / k) := by rw [hc₃]; ring
      _ ≤ c₃ * (ℓ ^ 8 * mertensSaving k ^ 2 / k) := by gcongr
  -- combine
  have hsq : (S₁ + S₂ + S₃) ^ 2 ≤ 3 * (|S₁| ^ 2 + |S₂| ^ 2 + |S₃| ^ 2) := by
    simp only [sq_abs]
    exact add_add_sq_le_three S₁ S₂ S₃
  have hsq₁ := pow_le_pow_left₀ (abs_nonneg S₁) hb₁ 2
  have hsq₂ := pow_le_pow_left₀ (abs_nonneg S₂) hb₂ 2
  have hsq₃ := pow_le_pow_left₀ (abs_nonneg S₃) hb₃ 2
  have hwk : 0 ≤ Real.exp 5 * (k : ℝ) ^ (4 + δ) := by positivity
  calc binomialWeight (5 + δ) k * (S₁ + S₂ + S₃) ^ 2
      ≤ Real.exp 5 * (k : ℝ) ^ (4 + δ) * (3 * (|S₁| ^ 2 + |S₂| ^ 2 + |S₃| ^ 2)) :=
        mul_le_mul hw hsq (sq_nonneg _) (hw0.trans hw)
    _ ≤ Real.exp 5 * (k : ℝ) ^ (4 + δ) * (3 * (
          (((H : ℝ) + 2) ^ (-(1 + δ)) * Real.exp (-(2 * k / ((H : ℝ) + 2))) / k) ^ 2 +
          (CB * mertensSaving L * ((L : ℝ) + 1) ^ (-(2 + δ)) *
            Real.exp (-(2 * k / ((L : ℝ) + 1)))) ^ 2 +
          (CH * mertensSaving U * (U : ℝ) ^ (-(2 + δ))) ^ 2)) := by gcongr
    _ = 3 * (Real.exp 5 * (k : ℝ) ^ (4 + δ) *
          (((H : ℝ) + 2) ^ (-(1 + δ)) * Real.exp (-(2 * k / ((H : ℝ) + 2))) / k) ^ 2 +
        Real.exp 5 * (k : ℝ) ^ (4 + δ) *
          (CB * mertensSaving L * ((L : ℝ) + 1) ^ (-(2 + δ)) *
            Real.exp (-(2 * k / ((L : ℝ) + 1)))) ^ 2 +
        Real.exp 5 * (k : ℝ) ^ (4 + δ) *
          (CH * mertensSaving U * (U : ℝ) ^ (-(2 + δ))) ^ 2) := by ring
    _ ≤ 3 * (c₁ * (ℓ ^ 8 * mertensSaving k ^ 2 / k) + c₂ * (ℓ ^ 8 * mertensSaving k ^ 2 / k) +
          c₃ * (ℓ ^ 8 * mertensSaving k ^ 2 / k)) := by gcongr
    _ = _ := by ring

/-- **Source-index aperture (7).**  For `0 < A ≤ 4` there are a threshold `k_A` and a constant
`C_A` such that `Σ_k C(4+δ+k, k) (c_k - c_k^mid)² ≤ C_A` for every cutoff `N` and `0 ≤ δ ≤ 1`. -/
theorem sourceAperture_bound {A : ℝ} (hA0 : 0 < A) (hA4 : A ≤ 4) :
    ∃ k₀ : ℕ, ∃ C : ℝ, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ N : ℕ,
      Summable (fun k => binomialWeight (5 + δ) k *
        (cubicPacket δ N k - middlePacket A δ k₀ N k) ^ 2) ∧
      ∑' k, binomialWeight (5 + δ) k * (cubicPacket δ N k - middlePacket A δ k₀ N k) ^ 2 ≤ C := by
  obtain ⟨k₁, C, hC, hpt⟩ := weighted_aperture_error_le hA0 hA4
  have hmaj := (summable_log_pow_mul_mertensSaving_sq_div 8).mul_left C
  refine ⟨k₁, ∑' k : ℕ, C * (Real.log k ^ 8 * mertensSaving k ^ 2 / k), fun δ hδ0 hδ1 N => ?_⟩
  have hle : ∀ k : ℕ, binomialWeight (5 + δ) k *
      (cubicPacket δ N k - middlePacket A δ k₁ N k) ^ 2 ≤
        C * (Real.log k ^ 8 * mertensSaving k ^ 2 / k) := by
    intro k
    unfold middlePacket
    split_ifs with hk
    · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      exact mul_nonneg hC.le (aperture_majorant_nonneg k)
    · exact hpt δ hδ0 hδ1 N k (not_lt.mp hk)
  have h0 : ∀ k : ℕ, 0 ≤ binomialWeight (5 + δ) k *
      (cubicPacket δ N k - middlePacket A δ k₁ N k) ^ 2 :=
    fun k => mul_nonneg (binomialWeight_nonneg (by linarith) k) (sq_nonneg _)
  have hs := Summable.of_nonneg_of_le h0 hle hmaj
  exact ⟨hs, hs.tsum_le_tsum hle hmaj⟩

/-- **Absolute high edge beyond `k^{a_δ + ε}`.**  Without the Mertens saving the high window
`n > ⌈k^{a_δ+ε}⌉` still has a bounded weighted square sum, uniformly in `N` and `0 ≤ δ ≤ 1`. -/
theorem absoluteHighEdge_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ N : ℕ,
      Summable (fun k : ℕ => binomialWeight (5 + δ) k *
        (∑ n ∈ Ioc (min N ⌈(k : ℝ) ^ (upperExponent δ + ε)⌉₊) N,
          ((μ n : ℤ) : ℝ) * packetKernel δ k n) ^ 2) ∧
      ∑' k : ℕ, binomialWeight (5 + δ) k *
        (∑ n ∈ Ioc (min N ⌈(k : ℝ) ^ (upperExponent δ + ε)⌉₊) N,
          ((μ n : ℤ) : ℝ) * packetKernel δ k n) ^ 2 ≤ C := by
  have hmaj : Summable (fun k : ℕ => Real.exp 5 * ((k : ℝ) ^ (1 + 4 * ε))⁻¹ + (if k = 0 then 3 else 0)) := by
    refine ((Real.summable_nat_rpow_inv.mpr (by linarith)).mul_left _).add ?_
    exact summable_of_ne_finset_zero (s := {0}) (fun k hk => by simp at hk; simp [hk])
  refine ⟨∑' k : ℕ, (Real.exp 5 * ((k : ℝ) ^ (1 + 4 * ε))⁻¹ + (if k = 0 then 3 else 0)),
    fun δ hδ0 hδ1 N => ?_⟩
  have hle : ∀ k : ℕ, binomialWeight (5 + δ) k *
      (∑ n ∈ Ioc (min N ⌈(k : ℝ) ^ (upperExponent δ + ε)⌉₊) N,
        ((μ n : ℤ) : ℝ) * packetKernel δ k n) ^ 2 ≤
        Real.exp 5 * ((k : ℝ) ^ (1 + 4 * ε))⁻¹ + (if k = 0 then 3 else 0) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- at `k = 0` the window is `n > 1`, and the kernel has no oscillation to exploit
      simp only [CharP.cast_eq_zero, ↓reduceIte]
      rw [Real.zero_rpow (by have := one_le_upperExponent hδ0 hδ1; linarith), Nat.ceil_zero,
        min_eq_right (Nat.zero_le N)]
      have h := abs_cubicPacket_le hδ0 N 0
      simp only [CharP.cast_eq_zero, mul_zero, zero_div, neg_zero, Real.exp_zero, mul_one] at h
      unfold binomialWeight
      simp only [Ring.choose_zero_right, one_mul]
      have hsq : (∑ n ∈ Ioc 0 N, ((μ n : ℤ) : ℝ) * packetKernel δ 0 n) ^ 2 ≤ (3 / 2) ^ 2 :=
        by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
      have : (0 : ℝ) ^ (1 + 4 * ε) = 0 := Real.zero_rpow (by linarith)
      simp only [this, inv_zero, mul_zero, zero_add]
      nlinarith [hsq]
    · have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hk0 : (0 : ℝ) < k := by linarith
      set V : ℕ := ⌈(k : ℝ) ^ (upperExponent δ + ε)⌉₊ with hV
      have ha := one_le_upperExponent hδ0 hδ1
      have hkV : (k : ℝ) ^ (upperExponent δ + ε) ≤ V := Nat.le_ceil _
      have hkk : (k : ℝ) ≤ (k : ℝ) ^ (upperExponent δ + ε) :=
        Real.self_le_rpow_of_one_le hk1r (by linarith)
      have hV1 : 1 ≤ V := by exact_mod_cast (hk1r.trans (hkk.trans hkV))
      have hV0 : (0 : ℝ) < V := by exact_mod_cast hV1
      -- absolute tail bound
      have habs : |∑ n ∈ Ioc (min N V) N, ((μ n : ℤ) : ℝ) * packetKernel δ k n| ≤
          (V : ℝ) ^ (-(2 + δ)) / 2 := by
        have hterm : ∀ n ∈ Ioc (min N V) N, |((μ n : ℤ) : ℝ) * packetKernel δ k n| ≤
            (n : ℝ) ^ (-((2 + δ) + 1)) := by
          intro n hn
          have hn1 : (1 : ℝ) ≤ n := by
            have := (mem_Ioc.mp hn).1
            exact_mod_cast (by omega : 1 ≤ n)
          rw [abs_mul, abs_of_nonneg (packetKernel_nonneg k hn1)]
          calc |((μ n : ℤ) : ℝ)| * packetKernel δ k n ≤ 1 * packetKernel δ k n :=
                mul_le_mul_of_nonneg_right (abs_moebius_le_one' n) (packetKernel_nonneg k hn1)
            _ ≤ ((n : ℝ) + 1) ^ (-(3 + δ)) * 1 := by
                rw [one_mul]
                refine (packetKernel_le k hn1).trans ?_
                gcongr
                rw [Real.exp_le_one_iff, neg_nonpos]
                positivity
            _ ≤ _ := by
                rw [mul_one, show -((2 + δ) + 1) = -(3 + δ) by ring]
                exact rpow_neg_le_of_le (by linarith) (by linarith) (by linarith)
        calc _ ≤ ∑ n ∈ Ioc (min N V) N, |((μ n : ℤ) : ℝ) * packetKernel δ k n| :=
              abs_sum_le_sum_abs _ _
          _ ≤ ∑ n ∈ Ioc (min N V) N, (n : ℝ) ^ (-((2 + δ) + 1)) := sum_le_sum hterm
          _ ≤ ∑ n ∈ Ioc V N, (n : ℝ) ^ (-((2 + δ) + 1)) := by
              rcases le_total N V with h | h
              · rw [min_eq_left h, Finset.Ioc_self, Finset.sum_empty]
                exact sum_nonneg fun n _ => Real.rpow_nonneg (by positivity) _
              · rw [min_eq_right h]
          _ ≤ (V : ℝ) ^ (-(2 + δ)) / (2 + δ) := sum_Ioc_rpow_neg_le (by linarith) hV1 N
          _ ≤ (V : ℝ) ^ (-(2 + δ)) / 2 :=
              div_le_div_of_nonneg_left (Real.rpow_nonneg hV0.le _) (by norm_num) (by linarith)
      have hw := binomialWeight_le_rpow hδ0 hδ1 hk
      have hw0 := binomialWeight_nonneg (show (0 : ℝ) ≤ 5 + δ by linarith) k
      have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
      rw [sq_abs] at hsq
      have hVk : (V : ℝ) ^ (-(2 + δ)) ≤ ((k : ℝ) ^ (upperExponent δ + ε)) ^ (-(2 + δ)) :=
        rpow_neg_le_of_le (Real.rpow_pos_of_pos hk0 _) hkV (by linarith)
      have hcrit : (k : ℝ) ^ (4 + δ) * (((k : ℝ) ^ (upperExponent δ + ε)) ^ (-(2 + δ))) ^ 2 =
          ((k : ℝ) ^ (1 + 2 * ε * (2 + δ)))⁻¹ := by
        rw [← Real.rpow_mul hk0.le, ← Real.rpow_natCast, ← Real.rpow_mul hk0.le,
          ← Real.rpow_add hk0, ← Real.rpow_neg hk0.le]
        congr 1
        have hm := upperExponent_mul hδ0
        push_cast
        nlinarith
      have hmono : ((k : ℝ) ^ (1 + 2 * ε * (2 + δ)))⁻¹ ≤ ((k : ℝ) ^ (1 + 4 * ε))⁻¹ := by
        apply inv_anti₀ (Real.rpow_pos_of_pos hk0 _)
        exact Real.rpow_le_rpow_of_exponent_le hk1r (by nlinarith)
      have hVk2 : ((V : ℝ) ^ (-(2 + δ)) / 2) ^ 2 ≤
          (((k : ℝ) ^ (upperExponent δ + ε)) ^ (-(2 + δ))) ^ 2 := by
        have h0 : 0 ≤ (V : ℝ) ^ (-(2 + δ)) / 2 := by
          have := Real.rpow_nonneg hV0.le (-(2 + δ)); positivity
        calc ((V : ℝ) ^ (-(2 + δ)) / 2) ^ 2 ≤ ((V : ℝ) ^ (-(2 + δ))) ^ 2 := by
              gcongr
              linarith [Real.rpow_nonneg hV0.le (-(2 + δ))]
          _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hV0.le _) hVk 2
      have hk0' : k ≠ 0 := by omega
      simp only [hk0', ↓reduceIte, add_zero]
      calc binomialWeight (5 + δ) k *
            (∑ n ∈ Ioc (min N V) N, ((μ n : ℤ) : ℝ) * packetKernel δ k n) ^ 2
          ≤ Real.exp 5 * (k : ℝ) ^ (4 + δ) * (((k : ℝ) ^ (upperExponent δ + ε)) ^ (-(2 + δ))) ^ 2 :=
            mul_le_mul hw (hsq.trans hVk2) (sq_nonneg _) (hw0.trans hw)
        _ = Real.exp 5 * ((k : ℝ) ^ (1 + 2 * ε * (2 + δ)))⁻¹ := by rw [mul_assoc, hcrit]
        _ ≤ Real.exp 5 * ((k : ℝ) ^ (1 + 4 * ε))⁻¹ := by gcongr
  have h0 : ∀ k : ℕ, 0 ≤ binomialWeight (5 + δ) k *
      (∑ n ∈ Ioc (min N ⌈(k : ℝ) ^ (upperExponent δ + ε)⌉₊) N,
        ((μ n : ℤ) : ℝ) * packetKernel δ k n) ^ 2 :=
    fun k => mul_nonneg (binomialWeight_nonneg (by linarith) k) (sq_nonneg _)
  have hs := Summable.of_nonneg_of_le h0 hle hmaj
  exact ⟨hs, hs.tsum_le_tsum hle hmaj⟩

/-! ### The critical wedge -/

/-- The wedge energy `Σ_{k₀ ≤ k < K(N)} w_k (Σ_{⌊4k/log k⌋ < n ≤ min(N, ⌈k^{a_δ}⌉)} μ(n) g_k(n))²`. -/
def wedgeEnergy (δ : ℝ) (k₀ N : ℕ) : ℝ :=
  ∑ k ∈ Ico k₀ (criticalHorizon N), binomialWeight (5 + δ) k * wedgePacket 4 δ N k ^ 2

theorem wedgeEnergy_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ) (k₀ N : ℕ) : 0 ≤ wedgeEnergy δ k₀ N :=
  sum_nonneg fun k _ => mul_nonneg (binomialWeight_nonneg (by linarith) k) (sq_nonneg _)

/-- Every finite cubic source is at most `N²`. -/
theorem routeLCubicEnergy_le_sq {δ : ℝ} (hδ0 : 0 ≤ δ) (N : ℕ) :
    finiteGeneralReciprocalEnergy (3 + δ) δ N ≤ (N : ℝ) ^ 2 := by
  unfold finiteGeneralReciprocalEnergy
  have hterm : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N,
      mobiusRealCoefficient m * mobiusRealCoefficient n *
        generalReciprocalMomentKernel (3 + δ) δ m n ≤ 1 := by
    intro m hm n hn
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [generalReciprocalMomentKernel_three_add_delta]
    have hs : (1 : ℝ) ≤ (m : ℝ) + n := by linarith
    have hK0 : 0 ≤ ((m : ℝ) * n) ^ 2 / ((m : ℝ) + n) ^ (5 + δ) := by positivity
    have hK1 : ((m : ℝ) * n) ^ 2 / ((m : ℝ) + n) ^ (5 + δ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      calc ((m : ℝ) * n) ^ 2 ≤ (((m : ℝ) + n) ^ 2) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity); nlinarith
        _ = ((m : ℝ) + n) ^ ((4 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; ring
        _ ≤ ((m : ℝ) + n) ^ (5 + δ) :=
            Real.rpow_le_rpow_of_exponent_le hs (by push_cast; linarith)
    have hμ : |mobiusRealCoefficient m * mobiusRealCoefficient n| ≤ 1 := by
      unfold mobiusRealCoefficient
      rw [abs_mul]
      have h1 : |((ArithmeticFunction.moebius m : ℤ) : ℝ)| ≤ 1 := abs_moebius_le_one' m
      have h2 : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := abs_moebius_le_one' n
      nlinarith [abs_nonneg ((ArithmeticFunction.moebius m : ℤ) : ℝ),
        abs_nonneg ((ArithmeticFunction.moebius n : ℤ) : ℝ)]
    have := abs_le.mp hμ
    nlinarith
  calc ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, mobiusRealCoefficient m * mobiusRealCoefficient n *
        generalReciprocalMomentKernel (3 + δ) δ m n
      ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (1 : ℝ) :=
        sum_le_sum fun m hm => sum_le_sum fun n hn => hterm m hm n hn
    _ = (N : ℝ) ^ 2 := by simp [sq]

/-- **Critical wedge criterion (8).**  With the sharp aperture `A = 4` there is a threshold `k₄`
such that, for every `0 ≤ δ ≤ 1` and every set of cutoffs, the cubic Route L source is bounded if
and only if the wedge energy is bounded. -/
theorem routeLCubicEnergy_bounded_iff_wedge :
    ∃ k₄ : ℕ, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ S : Set ℕ,
      (∃ B : ℝ, ∀ N ∈ S, finiteGeneralReciprocalEnergy (3 + δ) δ N ≤ B) ↔
        ∃ B : ℝ, ∀ N ∈ S, wedgeEnergy δ k₄ N ≤ B := by
  obtain ⟨k₄, C₄, hap⟩ := sourceAperture_bound (A := 4) (by norm_num) le_rfl
  obtain ⟨N₁, hN₁⟩ := cubicPacket_criticalTail_small 1 one_pos
  -- the horizon eventually passes `k₄`
  have hKev : ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → k₄ ≤ criticalHorizon N := by
    obtain ⟨N₂, hN₂⟩ := exists_nat_ge (Real.exp ((k₄ : ℝ) + 3))
    refine ⟨N₂, fun N hN => ?_⟩
    have hX : Real.exp ((k₄ : ℝ) + 3) ≤ (N : ℝ) + 1 := by
      have : (N₂ : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hℓ : (k₄ : ℝ) + 3 ≤ Real.log ((N : ℝ) + 1) := by
      rw [← Real.log_exp ((k₄ : ℝ) + 3)]
      exact Real.log_le_log (Real.exp_pos _) hX
    have h4 : (1 : ℝ) ≤ ((N : ℝ) + 1) / 4 := by
      have := Real.add_one_le_exp ((k₄ : ℝ) + 3)
      have : (0 : ℝ) ≤ k₄ := Nat.cast_nonneg k₄
      linarith
    have hl0 : 0 ≤ Real.log ((N : ℝ) + 1) := by linarith [(Nat.cast_nonneg k₄ : (0 : ℝ) ≤ k₄)]
    have h1 : (k₄ : ℝ) ≤ ((N : ℝ) + 1) / 4 * Real.log ((N : ℝ) + 1) := by
      have := mul_le_mul_of_nonneg_right h4 hl0
      linarith
    have h2 : (k₄ : ℝ) ≤ (criticalHorizon N : ℝ) := by
      unfold criticalHorizon
      exact h1.trans (Nat.le_ceil _)
    exact_mod_cast h2
  obtain ⟨N₂, hN₂⟩ := hKev
  refine ⟨k₄, fun δ hδ0 hδ1 S => ?_⟩
  have hs := fun N => (hap δ hδ0 hδ1 N).1
  have hC := fun N => (hap δ hδ0 hδ1 N).2
  have hsummE := summable_cubicPacket_energy hδ0 hδ1
  have h2 : (1 : ℝ) ≤ 2 ^ (5 + δ) := Real.one_le_rpow (by norm_num) (by linarith)
  have h2le : (2 : ℝ) ^ (5 + δ) ≤ 64 := by
    calc (2 : ℝ) ^ (5 + δ) ≤ 2 ^ ((6 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 64 := by rw [Real.rpow_natCast]; norm_num
  -- on the wedge, `(c^mid)² ≤ 2c² + 2(c - c^mid)²` and conversely
  have hmid : ∀ N k : ℕ, k₄ ≤ k → middlePacket 4 δ k₄ N k = wedgePacket 4 δ N k := by
    intro N k hk
    unfold middlePacket
    rw [if_neg (not_lt.mpr hk)]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨2 * B + 2 * C₄, fun N hN => ?_⟩
    have hE := routeLCubicEnergy_eq_cubicPacket N hδ0
    have hpt : ∀ k ∈ Ico k₄ (criticalHorizon N), binomialWeight (5 + δ) k *
        wedgePacket 4 δ N k ^ 2 ≤ 2 * (binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2) +
          2 * (binomialWeight (5 + δ) k *
            (cubicPacket δ N k - middlePacket 4 δ k₄ N k) ^ 2) := by
      intro k hk
      rw [hmid N k (mem_Ico.mp hk).1]
      have hw0 := binomialWeight_nonneg (show (0 : ℝ) ≤ 5 + δ by linarith) k
      have : wedgePacket 4 δ N k ^ 2 ≤ 2 * cubicPacket δ N k ^ 2 +
          2 * (cubicPacket δ N k - wedgePacket 4 δ N k) ^ 2 := by
        nlinarith [sq_nonneg (2 * cubicPacket δ N k - wedgePacket 4 δ N k)]
      nlinarith
    have hA := (hsummE N).sum_le_tsum (Ico k₄ (criticalHorizon N))
      (fun k _ => mul_nonneg (binomialWeight_nonneg (by linarith) k) (sq_nonneg _))
    have hB' := (hs N).sum_le_tsum (Ico k₄ (criticalHorizon N))
      (fun k _ => mul_nonneg (binomialWeight_nonneg (by linarith) k) (sq_nonneg _))
    have htsum0 : 0 ≤ ∑' k, binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2 :=
      tsum_nonneg fun k => mul_nonneg (binomialWeight_nonneg (by linarith) k) (sq_nonneg _)
    have hEle : ∑' k, binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2 ≤
        finiteGeneralReciprocalEnergy (3 + δ) δ N := by
      rw [hE]; nlinarith
    unfold wedgeEnergy
    calc _ ≤ ∑ k ∈ Ico k₄ (criticalHorizon N), (2 * (binomialWeight (5 + δ) k *
          cubicPacket δ N k ^ 2) + 2 * (binomialWeight (5 + δ) k *
            (cubicPacket δ N k - middlePacket 4 δ k₄ N k) ^ 2)) := sum_le_sum hpt
      _ = 2 * ∑ k ∈ Ico k₄ (criticalHorizon N), binomialWeight (5 + δ) k *
            cubicPacket δ N k ^ 2 + 2 * ∑ k ∈ Ico k₄ (criticalHorizon N),
              binomialWeight (5 + δ) k * (cubicPacket δ N k - middlePacket 4 δ k₄ N k) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * B + 2 * C₄ := by linarith [hB N hN, hC N]
  · rintro ⟨B, hB⟩
    set D : ℝ := ∑ k ∈ range k₄, binomialWeight 6 k * (9 / 4) with hD
    refine ⟨max ((max N₁ N₂ : ℕ) ^ 2 : ℝ) (64 * (D + 2 * B + 2 * C₄) + 1), fun N hN => ?_⟩
    rcases lt_or_ge N (max N₁ N₂) with hsmall | hlarge
    · refine (routeLCubicEnergy_le_sq hδ0 N).trans (le_max_of_le_left ?_)
      have : (N : ℝ) ≤ (max N₁ N₂ : ℕ) := by exact_mod_cast hsmall.le
      exact pow_le_pow_left₀ (Nat.cast_nonneg N) this 2
    refine le_max_of_le_right ?_
    have hK := hN₂ N (le_of_max_le_right hlarge)
    have htail := hN₁ δ hδ0 hδ1 N (le_of_max_le_left hlarge)
    rw [routeLCubicEnergy_eq_head_add_tail hδ0 hδ1 N (criticalHorizon N),
      ← Finset.sum_range_add_sum_Ico _ hK]
    -- the first packets
    have hlow : ∑ k ∈ range k₄, binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2 ≤ D := by
      rw [hD]
      apply sum_le_sum
      intro k _
      have hc := abs_cubicPacket_le hδ0 N k
      have hex : Real.exp (-(2 * k / ((N : ℝ) + 1))) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_nonpos]; positivity
      have hc' : |cubicPacket δ N k| ≤ 3 / 2 := by nlinarith
      have hsq : cubicPacket δ N k ^ 2 ≤ 9 / 4 := by
        rw [← sq_abs]
        calc |cubicPacket δ N k| ^ 2 ≤ (3 / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hc' 2
          _ = 9 / 4 := by norm_num
      have hw := binomialWeight_mono (show (0 : ℝ) ≤ 5 + δ by linarith)
        (show 5 + δ ≤ (6 : ℝ) by linarith) k
      have hw0 := binomialWeight_nonneg (show (0 : ℝ) ≤ 5 + δ by linarith) k
      exact mul_le_mul hw hsq (sq_nonneg _) (hw0.trans hw)
    -- the wedge range
    have hwedge : ∑ k ∈ Ico k₄ (criticalHorizon N), binomialWeight (5 + δ) k *
        cubicPacket δ N k ^ 2 ≤ 2 * B + 2 * C₄ := by
      have hpt : ∀ k ∈ Ico k₄ (criticalHorizon N), binomialWeight (5 + δ) k *
          cubicPacket δ N k ^ 2 ≤ 2 * (binomialWeight (5 + δ) k * wedgePacket 4 δ N k ^ 2) +
            2 * (binomialWeight (5 + δ) k *
              (cubicPacket δ N k - middlePacket 4 δ k₄ N k) ^ 2) := by
        intro k hk
        rw [hmid N k (mem_Ico.mp hk).1]
        have hw0 := binomialWeight_nonneg (show (0 : ℝ) ≤ 5 + δ by linarith) k
        have : cubicPacket δ N k ^ 2 ≤ 2 * wedgePacket 4 δ N k ^ 2 +
            2 * (cubicPacket δ N k - wedgePacket 4 δ N k) ^ 2 := by
          nlinarith [sq_nonneg (2 * wedgePacket 4 δ N k - cubicPacket δ N k)]
        nlinarith
      have hB' := (hs N).sum_le_tsum (Ico k₄ (criticalHorizon N))
        (fun k _ => mul_nonneg (binomialWeight_nonneg (by linarith) k) (sq_nonneg _))
      calc _ ≤ ∑ k ∈ Ico k₄ (criticalHorizon N), (2 * (binomialWeight (5 + δ) k *
            wedgePacket 4 δ N k ^ 2) + 2 * (binomialWeight (5 + δ) k *
              (cubicPacket δ N k - middlePacket 4 δ k₄ N k) ^ 2)) := sum_le_sum hpt
        _ = 2 * wedgeEnergy δ k₄ N + 2 * ∑ k ∈ Ico k₄ (criticalHorizon N),
              binomialWeight (5 + δ) k * (cubicPacket δ N k - middlePacket 4 δ k₄ N k) ^ 2 := by
            unfold wedgeEnergy
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ 2 * B + 2 * C₄ := by linarith [hB N hN, hC N]
    have hhead0 : 0 ≤ D + 2 * B + 2 * C₄ := by
      have h1 : 0 ≤ ∑ k ∈ range k₄, binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2 :=
        sum_nonneg fun k _ => mul_nonneg (binomialWeight_nonneg (by linarith) k) (sq_nonneg _)
      have h2' : 0 ≤ ∑ k ∈ Ico k₄ (criticalHorizon N), binomialWeight (5 + δ) k *
          cubicPacket δ N k ^ 2 :=
        sum_nonneg fun k _ => mul_nonneg (binomialWeight_nonneg (by linarith) k) (sq_nonneg _)
      linarith
    calc 2 ^ (5 + δ) * (∑ k ∈ range k₄, binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2 +
          ∑ k ∈ Ico k₄ (criticalHorizon N), binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2) +
        2 ^ (5 + δ) * ∑' j : ℕ, binomialWeight (5 + δ) (j + criticalHorizon N) *
          cubicPacket δ N (j + criticalHorizon N) ^ 2
        ≤ 64 * (D + 2 * B + 2 * C₄) + 1 := by
          have := add_le_add hlow hwedge
          have hle : 2 ^ (5 + δ) * (∑ k ∈ range k₄, binomialWeight (5 + δ) k *
              cubicPacket δ N k ^ 2 + ∑ k ∈ Ico k₄ (criticalHorizon N),
                binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2) ≤
              64 * (D + 2 * B + 2 * C₄) := by
            calc _ ≤ 2 ^ (5 + δ) * (D + (2 * B + 2 * C₄)) :=
                  mul_le_mul_of_nonneg_left this (by positivity)
              _ ≤ 64 * (D + 2 * B + 2 * C₄) := by
                  rw [← add_assoc]
                  exact mul_le_mul_of_nonneg_right h2le hhead0
          linarith

/-- **Wedge receiver.**  Bounded returns of the critical wedge energy on shifts cofinal at zero
imply RH. -/
theorem riemannHypothesis_of_wedgeEnergyFrequentlyBounded :
    ∃ k₄ : ℕ, (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < 2 * ε ∧ ∃ B : ℝ,
      ∃ᶠ N : ℕ in atTop, wedgeEnergy δ k₄ N ≤ B) → RiemannHypothesis := by
  obtain ⟨k₄, hiff⟩ := routeLCubicEnergy_bounded_iff_wedge
  refine ⟨k₄, fun h => ?_⟩
  apply riemannHypothesis_of_routeLCofinalCubicEnergyFrequentlyBounded
  intro ε hε
  obtain ⟨δ, hδ, hδε, B, hfreq⟩ := h (min ε (1 / 2)) (lt_min hε (by norm_num))
  have hδ1 : δ ≤ 1 := by
    have := min_le_right ε (1 / 2 : ℝ)
    linarith
  have hδε' : δ < 2 * ε := by
    have := min_le_left ε (1 / 2 : ℝ)
    linarith
  obtain ⟨B', hB'⟩ := (hiff δ hδ.le hδ1 {N | wedgeEnergy δ k₄ N ≤ B}).mpr ⟨B, fun N hN => hN⟩
  exact ⟨δ, hδ, hδε', B', hfreq.mono fun N hN => hB' N hN⟩

end RHTower.DiscretePacket
