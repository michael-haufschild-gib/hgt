import GaloisForLFunctions.RHTower.WeilMixedResonanceLockSpectrum

/-!
# Almost-periodic locks whose rational resonances are integral

**Theorem** (`integer_resonant_lock_rigidity`).  Let `G` be a Herglotz producer for the weights
`lam`.  Suppose that on the lower critical line

`G(1 − s) = (Σ_k P(k) k^{−(s−½)} + Σ_j q_j ρ_j^{−(s−½)}) G(s)`,

where `Σ_k |P(k)| < ∞`, `ρ_j > 0`, `Σ_j |q_j| max(1, ρ_j^{−1}) < ∞`, and no `ρ_j` is rational.
Then `lam(n) = Λ(n)` for all `n ≥ 2`, and the Riemann hypothesis holds.

On the line `s = ½ − iy` the lock factor is an almost-periodic function with frequencies `log k`
and `log ρ_j`.  A frequency `log r` resonates with the producer's Dirichlet series exactly when
`r ∈ ℚ_{>0}`.  The theorem covers every spectrum whose resonant part is integral.  It contains
`ap_lock_rigidity` (resonant part `{0}`) and `dirichlet_lock_rigidity` (no non-resonant part).

**Theorem** (`aggregated_resonant_lock_rigidity`).  The same holds when the `ρ_j` are arbitrary
positive reals whose coefficients, aggregated at every positive rational value, vanish.

**Proof.**
1. The Abel spectrum of the non-rational sum vanishes (`tendsto_apLock_abel`), so the divisor
   system and the factorization `G V_ℕ = 2G(1) ξ` hold for the integral part
   `V_ℕ = Σ P(k) k^{−(s−½)}` alone.
2. On the line, `G(s̄) = conj G(s)`, the lock `conj G = V G` and the reality of `ξ` give
   `V · conj V_ℕ = κ V_ℕ` with `κ = conj G(1)/G(1)`: first where `ξ ≠ 0`, then everywhere by
   continuity, since the zeros of `ξ` are isolated.
3. Bohr means of this identity at the frequencies `± log k`, `k ≥ 2`: the non-resonant products
   `V_N · conj V_ℕ` have no mean at these frequencies.  At `−log k` the identity gives
   `Σ_a P(a) conj P(ka) = 0`; at `+log k` it gives `κ P(k) = Σ_b P(kb) conj P(b)`, which is the
   conjugate of the former.  So `P(k) = 0` for `k ≥ 2`.
4. Then `V_ℕ = P(1)`, so `G = (2G(1)/P(1)) ξ` on `Re s ≥ ½`.  This is a constant lock, and
   `phase_lock_rigidity` applies.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-! ### Line expansions -/

/-- The coefficients `P(k)` with the `k = 0` entry removed. -/
def natCoeff (P : ℕ → ℂ) (k : ℕ) : ℂ := if k = 0 then 0 else P k

theorem norm_natCoeff_le (P : ℕ → ℂ) (k : ℕ) : ‖natCoeff P k‖ ≤ ‖P k‖ := by
  unfold natCoeff; split_ifs <;> simp

theorem dirLock_line (P : ℕ → ℂ) (y : ℝ) :
    dirLock P (1 / 2 - (y : ℂ) * I) =
      ∑' k, natCoeff P k * cexp (((Real.log k : ℝ) : ℂ) * I * y) := by
  rw [dirLock_of_le P (by simp), LSeries]
  congr 1; funext k
  rcases eq_or_ne k 0 with rfl | hk
  · simp [natCoeff]
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [LSeries.term_of_ne_zero hk, natCoeff, if_neg hk,
    show (1 / 2 - (y : ℂ) * I - 1 / 2) = -((y : ℂ) * I) by ring, Complex.cpow_neg,
    div_inv_eq_mul, Complex.cpow_def_of_ne_zero hk0, ← Complex.natCast_log]
  ring_nf

theorem apLock_line (q : ℕ → ℂ) {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j) (y : ℝ) :
    apLock q ρ (1 / 2 - (y : ℂ) * I) =
      ∑' j, q j * cexp (((Real.log (ρ j) : ℝ) : ℂ) * I * y) := by
  rw [apLock_of_mem q ρ (by simp) (by simp; norm_num)]
  congr 1; funext j
  have hb : (ρ j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hρ j).ne'
  rw [show -(1 / 2 - (y : ℂ) * I - 1 / 2) = (y : ℂ) * I by ring,
    Complex.cpow_def_of_ne_zero hb, ← Complex.ofReal_log (hρ j).le]
  ring_nf

theorem conj_tsum_exp (c : ℕ → ℂ) (θ : ℕ → ℝ) (y : ℝ) :
    conj (∑' k, c k * cexp ((θ k : ℂ) * I * y)) =
      ∑' k, conj (c k) * cexp (((-θ k : ℝ) : ℂ) * I * y) := by
  rw [Complex.conj_tsum]
  congr 1; funext k
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/-- The product of two absolutely convergent exponential sums, shifted by `e^{−iωy}`. -/
theorem tsum_exp_mul_tsum_exp {ι ι' : Type*} {c : ι → ℂ} {d : ι' → ℂ}
    (hc : Summable fun i => ‖c i‖) (hd : Summable fun i => ‖d i‖) (θ : ι → ℝ) (φ : ι' → ℝ)
    (ω y : ℝ) :
    (∑' i, c i * cexp ((θ i : ℂ) * I * y)) * (∑' i, d i * cexp ((φ i : ℂ) * I * y)) *
        cexp (((-ω : ℝ) : ℂ) * I * y) =
      ∑' z : ι × ι', c z.1 * d z.2 * cexp (((θ z.1 + φ z.2 - ω : ℝ) : ℂ) * I * y) := by
  have hn : ∀ (r : ℝ), ‖cexp ((r : ℂ) * I * y)‖ = 1 := by
    intro r; rw [Complex.norm_exp]; simp
  have hc' : Summable fun i => ‖c i * cexp ((θ i : ℂ) * I * y)‖ := by
    simpa [norm_mul, hn] using hc
  have hd' : Summable fun i => ‖d i * cexp ((φ i : ℂ) * I * y)‖ := by
    simpa [norm_mul, hn] using hd
  rw [tsum_mul_tsum_of_summable_norm hc' hd', ← tsum_mul_right]
  congr 1; funext z
  have : cexp (((θ z.1 + φ z.2 - ω : ℝ) : ℂ) * I * y) =
      cexp ((θ z.1 : ℂ) * I * y) * cexp ((φ z.2 : ℂ) * I * y) * cexp (((-ω : ℝ) : ℂ) * I * y) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [this]; ring

theorem tsum_exp_mul_exp {ι : Type*} (c : ι → ℂ) (θ : ι → ℝ) (ω y : ℝ) :
    (∑' i, c i * cexp ((θ i : ℂ) * I * y)) * cexp (((-ω : ℝ) : ℂ) * I * y) =
      ∑' i, c i * cexp (((θ i - ω : ℝ) : ℂ) * I * y) := by
  rw [← tsum_mul_right]
  congr 1; funext i
  rw [mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring

theorem continuous_tsum_exp {ι : Type*} {c : ι → ℂ} (hc : Summable fun i => ‖c i‖) (θ : ι → ℝ) :
    Continuous fun y : ℝ => ∑' i, c i * cexp ((θ i : ℂ) * I * y) := by
  refine continuous_tsum (fun i => by fun_prop) hc (fun i y => ?_)
  rw [norm_mul, Complex.norm_exp]; simp

/-! ### The coefficient argument -/

theorem summable_natCoeff {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) :
    Summable fun k => ‖natCoeff P k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_natCoeff_le P) hP

/-- **Bohr-mean identity.**  If `A + B − κ C ≡ 0` on `(0, ∞)` for three absolutely convergent
exponential sums, then the zero-frequency coefficients satisfy the same relation. -/
theorem mean_coeff_relation {ι₁ ι₂ ι₃ : Type*} [Countable ι₁] [Countable ι₂] [Countable ι₃]
    {a : ι₁ → ℂ} {b : ι₂ → ℂ} {c : ι₃ → ℂ} (ha : Summable fun i => ‖a i‖)
    (hb : Summable fun i => ‖b i‖) (hc : Summable fun i => ‖c i‖) (α : ι₁ → ℝ) (β : ι₂ → ℝ)
    (γ : ι₃ → ℝ) (κ : ℂ)
    (h : ∀ y : ℝ, 0 < y → (∑' i, a i * cexp ((α i : ℂ) * I * y)) +
      (∑' i, b i * cexp ((β i : ℂ) * I * y)) - κ * (∑' i, c i * cexp ((γ i : ℂ) * I * y)) = 0) :
    (∑' i, if α i = 0 then a i else 0) + (∑' i, if β i = 0 then b i else 0) -
      κ * (∑' i, if γ i = 0 then c i else 0) = 0 := by
  have hA := tendsto_mean_expSum ha α
  have hB := tendsto_mean_expSum hb β
  have hC := tendsto_mean_expSum hc γ
  have hsum := (hA.add hB).sub (hC.const_mul κ)
  refine tendsto_nhds_unique hsum (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hcA := (continuous_tsum_exp ha α).intervalIntegrable (μ := volume) 0 T
  have hcB := (continuous_tsum_exp hb β).intervalIntegrable (μ := volume) 0 T
  have hcC := (continuous_tsum_exp hc γ).intervalIntegrable (μ := volume) 0 T
  have hzero : ∫ y in (0 : ℝ)..T, ((∑' i, a i * cexp ((α i : ℂ) * I * y)) +
      (∑' i, b i * cexp ((β i : ℂ) * I * y)) - κ * (∑' i, c i * cexp ((γ i : ℂ) * I * y))) = 0 := by
    rw [intervalIntegral.integral_of_le hT.le]
    refine (setIntegral_congr_fun measurableSet_Ioc fun y hy => h y hy.1).trans ?_
    simp
  rw [intervalIntegral.integral_sub (hcA.add hcB) (hcC.const_mul κ),
    intervalIntegral.integral_add hcA hcB, intervalIntegral.integral_const_mul] at hzero
  linear_combination (-(1 / (T : ℂ))) * hzero

theorem log_natCast_inj {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : Real.log a = Real.log b) :
    a = b := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
  exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr ha') (Set.mem_Ioi.mpr hb') h

/-- **Integer coefficients vanish.**  If `(V_ℕ + V_N) conj V_ℕ = κ V_ℕ` on the critical line, where
the coefficients of `V_N` aggregated at every positive rational vanish and `κ ≠ 0`, then `P(k) = 0`
for every `k ≥ 2`. -/
theorem natCoeff_eq_zero_of_line_identity {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) {q : ℕ → ℂ}
    {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j) (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹)
    (hagg : ∀ a b : ℕ, 0 < b → (∑' j, if (b : ℝ) * ρ j = a then q j else 0) = 0) {κ : ℂ}
    (hκ : κ ≠ 0)
    (hid : ∀ y : ℝ, 0 < y → (dirLock P (1 / 2 - (y : ℂ) * I) + apLock q ρ (1 / 2 - (y : ℂ) * I)) *
      conj (dirLock P (1 / 2 - (y : ℂ) * I)) = κ * dirLock P (1 / 2 - (y : ℂ) * I))
    {k : ℕ} (hk : 2 ≤ k) : P k = 0 := by
  set c : ℕ → ℂ := natCoeff P with hc_def
  have hc : Summable fun i => ‖c i‖ := summable_natCoeff hP
  have hcc : Summable fun i => ‖conj (c i)‖ := by simpa using hc
  have hqn : Summable fun j => ‖q j‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => le_mul_of_one_le_right (norm_nonneg _) (le_max_left _ _)) hq
  set θ : ℕ → ℝ := fun k => Real.log k with hθ
  set lq : ℕ → ℝ := fun j => Real.log (ρ j) with hlq
  have hk0 : k ≠ 0 := by omega
  have hlogk : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  -- the identity multiplied by `e^{−iωy}`, expanded
  have hexp : ∀ ω : ℝ, ∀ y : ℝ, 0 < y →
      (∑' z : ℕ × ℕ, c z.1 * conj (c z.2) * cexp (((θ z.1 + -θ z.2 - ω : ℝ) : ℂ) * I * y)) +
      (∑' z : ℕ × ℕ, q z.1 * conj (c z.2) * cexp (((lq z.1 + -θ z.2 - ω : ℝ) : ℂ) * I * y)) -
      κ * (∑' i, c i * cexp (((θ i - ω : ℝ) : ℂ) * I * y)) = 0 := by
    intro ω y hy
    have h := hid y hy
    rw [dirLock_line, apLock_line q hρ, conj_tsum_exp] at h
    have h' := congrArg (· * cexp (((-ω : ℝ) : ℂ) * I * y)) h
    rw [add_mul, add_mul, tsum_exp_mul_tsum_exp hc hcc, tsum_exp_mul_tsum_exp hqn hcc,
      mul_assoc, tsum_exp_mul_exp] at h'
    rw [h']; ring
  have hrel := fun ω : ℝ => mean_coeff_relation (hc.mul_norm hcc) (hqn.mul_norm hcc) hc _ _ _ κ
    (hexp ω)
  -- frequency `−log k`
  have hneg := hrel (-Real.log k)
  have hB0 : ∀ ω : ℝ, (ω = Real.log k ∨ ω = -Real.log k) →
      (∑' z : ℕ × ℕ, if lq z.1 + -θ z.2 - ω = 0 then q z.1 * conj (c z.2) else 0) = 0 := by
    intro ω hω
    have hk0' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
    set f : ℕ × ℕ → ℂ := fun z => if lq z.1 + -θ z.2 - ω = 0 then q z.1 * conj (c z.2) else 0
      with hf
    have hfs : Summable fun z : ℕ × ℕ => f (Equiv.prodComm ℕ ℕ z) := by
      refine Summable.of_norm_bounded ((hcc.mul_norm hqn)) fun z => ?_
      simp only [hf, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      split_ifs
      · rw [norm_mul, norm_mul, mul_comm]
      · rw [norm_zero]; positivity
    rw [← (Equiv.prodComm ℕ ℕ).tsum_eq, hfs.tsum_prod]
    refine (tsum_congr fun b => ?_).trans tsum_zero
    simp only [hf, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rcases eq_or_ne b 0 with hb | hb
    · simp [hc_def, natCoeff, hb]
    have hb0 : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
    have hsplit : (fun j => if lq j + -θ b - ω = 0 then q j * conj (c b) else 0) =
        fun j => (if lq j + -θ b - ω = 0 then q j else 0) * conj (c b) := by
      funext j; split_ifs <;> simp
    rw [hsplit, tsum_mul_right]
    refine mul_eq_zero_of_left ?_ _
    rcases hω with rfl | rfl
    · -- `ρ_j = b k`
      have hcond : ∀ j, (lq j + -θ b - Real.log k = 0 ↔ ((1 : ℕ) : ℝ) * ρ j = ((b * k : ℕ) : ℝ)) := by
        intro j
        constructor
        · intro h0
          have hl : Real.log (ρ j) = Real.log ((b : ℝ) * k) := by
            rw [Real.log_mul hb0.ne' hk0'.ne']; simp only [hlq, hθ] at h0; linarith
          have := Real.log_injOn_pos (Set.mem_Ioi.mpr (hρ j)) (Set.mem_Ioi.mpr (mul_pos hb0 hk0')) hl
          push_cast; rw [this]; ring
        · intro h0
          push_cast at h0
          simp only [hlq, hθ]
          rw [one_mul] at h0
          rw [h0, Real.log_mul hb0.ne' hk0'.ne']; ring
      rw [tsum_congr fun j => if_congr (hcond j) rfl rfl]
      exact hagg _ 1 one_pos
    · -- `k ρ_j = b`
      have hcond : ∀ j, (lq j + -θ b - -Real.log k = 0 ↔ (k : ℝ) * ρ j = (b : ℝ)) := by
        intro j
        constructor
        · intro h0
          have hl : Real.log ((k : ℝ) * ρ j) = Real.log (b : ℝ) := by
            rw [Real.log_mul hk0'.ne' (hρ j).ne']; simp only [hlq, hθ] at h0; linarith
          exact Real.log_injOn_pos (Set.mem_Ioi.mpr (mul_pos hk0' (hρ j))) (Set.mem_Ioi.mpr hb0) hl
        · intro h0
          simp only [hlq, hθ]
          have : Real.log (ρ j) = Real.log b - Real.log k := by
            rw [← h0, Real.log_mul hk0'.ne' (hρ j).ne']; ring
          rw [this]; ring
      rw [tsum_congr fun j => if_congr (hcond j) rfl rfl]
      exact hagg _ _ (Nat.pos_of_ne_zero hk0)
  have hC_neg : (∑' i, if θ i - -Real.log k = 0 then c i else 0) = 0 := by
    refine (tsum_congr fun i => ?_).trans tsum_zero
    split_ifs with h0
    · rcases eq_or_ne i 0 with hi | hi
      · simp [hc_def, natCoeff, hi]
      exfalso
      have := Real.log_natCast_nonneg i
      simp only [hθ] at h0
      linarith
    · rfl
  rw [hB0 _ (Or.inr rfl), hC_neg, mul_zero, add_zero, sub_zero] at hneg
  -- frequency `+log k`
  have hpos := hrel (Real.log k)
  have hC_pos : (∑' i, if θ i - Real.log k = 0 then c i else 0) = P k := by
    rw [tsum_eq_single k]
    · simp [hθ, hc_def, natCoeff, hk0]
    · intro i hi
      rw [if_neg]
      intro h0
      rcases eq_or_ne i 0 with hi0 | hi0
      · subst hi0; simp only [hθ, Nat.cast_zero, Real.log_zero] at h0; linarith
      · exact hi (log_natCast_inj hi0 hk0 (by simp only [hθ] at h0; linarith))
  rw [hB0 _ (Or.inl rfl), hC_pos, add_zero] at hpos
  -- the two resonant sums are conjugate
  have hswap : (∑' z : ℕ × ℕ, if θ z.1 + -θ z.2 - Real.log k = 0 then c z.1 * conj (c z.2) else 0) =
      conj (∑' z : ℕ × ℕ, if θ z.1 + -θ z.2 - -Real.log k = 0 then c z.1 * conj (c z.2) else 0) := by
    rw [Complex.conj_tsum, ← (Equiv.prodComm ℕ ℕ).tsum_eq]
    congr 1; funext z
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    by_cases h0 : θ z.2 + -θ z.1 - Real.log k = 0
    · rw [if_pos h0, if_pos (by linarith), map_mul, Complex.conj_conj, mul_comm]
    · rw [if_neg h0, if_neg (by intro h1; exact h0 (by linarith)), map_zero]
  rw [hswap, hneg, map_zero, zero_sub, neg_eq_zero] at hpos
  exact (mul_eq_zero.mp hpos).resolve_left hκ

theorem dirLock_eq_coeff_one {P : ℕ → ℂ} (hP2 : ∀ k, 2 ≤ k → P k = 0) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) : dirLock P s = P 1 := by
  rw [dirLock_of_le P hs, LSeries, tsum_eq_single 1]
  · simp
  · intro k hk
    rcases eq_or_ne k 0 with rfl | hk0
    · simp
    · rw [LSeries.term_of_ne_zero hk0, hP2 k (by omega), zero_div]

/-! ### The rigidity theorem -/

/-- A bounded continuous lock factor times `e^{yw}` is integrable on the edge half-line, `Re w > 0`. -/
theorem integrableOn_edge_mul_exp {V : ℂ → ℂ} (hV : Continuous V) {C : ℝ}
    (hb : ∀ s, ‖V s‖ ≤ C) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun y : ℝ => V (edgePt y) * cexp ((y : ℂ) * w)) (Iic (-2 : ℝ)) := by
  have hexpInt : IntegrableOn (fun y : ℝ => Real.exp (w.re * y)) (Iic (-2 : ℝ)) := by
    have h : IntegrableOn (fun y : ℝ => ‖cexp ((w.re : ℂ) * (y : ℂ))‖) (Iic (-2 : ℝ)) :=
      (integrableOn_exp_mul_complex_Iic (a := (w.re : ℂ)) (by simpa using hw) (-2)).norm
    refine h.congr_fun (fun y _ => ?_) measurableSet_Iic
    simp only
    rw [Complex.norm_exp]
    congr 1; simp
  have hc : Continuous fun y : ℝ => V (edgePt y) * cexp ((y : ℂ) * w) :=
    (hV.comp continuous_edgePt).mul (by fun_prop)
  refine (hexpInt.const_mul C).mono' hc.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_exp]
  have : ((y : ℂ) * w).re = w.re * y := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (hb _) (Real.exp_pos _).le

/-- **Almost-periodic locks with integral resonances force the true producer**, in the form where
the second family has vanishing aggregated coefficients at every positive rational. -/
theorem aggregated_resonant_lock_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹)
    (hagg : ∀ a b : ℕ, 0 < b → (∑' j, if (b : ℝ) * ρ j = a then q j else 0) = 0)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      (LSeries P (lineS τ - 1 / 2) + ∑' j, q j * (ρ j : ℂ) ^ (-(lineS τ - 1 / 2))) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  set V : ℂ → ℂ := fun s => dirLock P s + apLock q ρ s with hV
  have hVcont : Continuous V := (continuous_dirLock hP).add (continuous_apLock hρ hq)
  set S : ℝ := (∑' k, ‖P k‖) + ∑' j, ‖q j‖ * max 1 (ρ j)⁻¹ with hS
  have hS0 : 0 ≤ S := add_nonneg (tsum_nonneg fun k => norm_nonneg _)
    (tsum_nonneg fun j => mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))
  have hVb : ∀ s, ‖V s‖ ≤ S := fun s =>
    (norm_add_le _ _).trans (add_le_add (norm_dirLock_le hP s) (norm_apLock_le hρ hq s))
  have hbd : ∀ s, ‖V s‖ ≤ Real.exp (Real.log (S + 1)) := fun s => by
    rw [Real.exp_log (by linarith)]; linarith [hVb s]
  have hlockV : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = V (lineS τ) * G (lineS τ) := by
    intro τ hτ
    rw [hV]; simp only
    rw [dirLock_of_le P (le_of_eq (lineS_re τ).symm),
      apLock_of_mem q ρ (le_of_eq (lineS_re τ).symm) (by rw [lineS_re]; norm_num)]
    exact hlock τ hτ
  -- the Abel spectrum of `V` is that of its integral part
  have hspec : ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, 1 ≤ n → Tendsto (fun ε : ℝ => (ε : ℂ) *
      ∫ y in Iic (-2 : ℝ), V (edgePt y) * cexp ((y : ℂ) *
        (edgeExp ((ε : ℂ) + (m : ℂ) * I) - ((Real.log n : ℝ) : ℂ) * I))) (𝓝[>] 0)
      (𝓝 (dirSpec P m n)) := by
    intro m hm n hn
    have h := (tendsto_dirLock_abel hP hm hn).add
      (tendsto_apLock_abel hρ hq hm hn (hagg m n (by omega)))
    rw [add_zero] at h
    refine h.congr' ?_
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have h1 : (0 : ℝ) < 1 / m := div_pos one_pos hm0
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_re_edgeExp_div hm).eventually (lt_mem_nhds h1)] with ε hε hr
    have hpos : 0 < (edgeExp ((ε : ℂ) + (m : ℂ) * I)).re :=
      (div_pos_iff_of_pos_right (show (0 : ℝ) < ε from hε)).mp hr
    have hw : 0 < (edgeExp ((ε : ℂ) + (m : ℂ) * I) - ((Real.log n : ℝ) : ℂ) * I).re := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      linarith
    have hi1 := integrableOn_edge_mul_exp (continuous_dirLock hP) (norm_dirLock_le hP) hw
    have hi2 := integrableOn_edge_mul_exp (continuous_apLock hρ hq) (norm_apLock_le hρ hq) hw
    simp only [hV, add_mul]
    rw [integral_add hi1 hi2, mul_add]
  have hsys : ∀ m : ℕ, 1 ≤ m → ((Real.sqrt m : ℝ) : ℂ) *
      LSeries.convolution (halfCoeff (dirichletExp (lamLog lam))) P m = G 1 := fun m hm =>
    divisor_system_of_spec hsl hΦd hΦre hid hGc hGd hG2 (V := V)
      (fun s _ _ _ => hVcont.continuousAt)
      (fun s h1 h2 _ => (differentiableAt_dirLock hP h1).add (differentiableAt_apLock hρ hq h1 h2))
      (fun s _ _ _ => hbd s) (fun t _ => hbd _) hlockV hm (hspec m hm)
  have hF := fun {s : ℂ} (hs : 1 / 2 ≤ s.re) => G_mul_dirLock_eq_xi hsl hid hGc hGd hG2 hP hsys hs
  have hG1 : G 1 ≠ 0 := G_ne_zero hΦd hGd hG2 (ρ := 1) (by norm_num)
  set κ : ℂ := conj (G 1) / G 1 with hκ_def
  have hκ : κ ≠ 0 := div_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hG1) hG1
  have hκG : κ * G 1 = conj (G 1) := by rw [hκ_def]; field_simp
  -- the line identity `V conj V_ℕ = κ V_ℕ`
  set sl : ℝ → ℂ := fun y => 1 / 2 - (y : ℂ) * I with hsl_def
  have hsl_re : ∀ y, (sl y).re = 1 / 2 := fun y => by simp [hsl_def]
  set h : ℝ → ℂ := fun y => V (sl y) * conj (dirLock P (sl y)) - κ * dirLock P (sl y) with hh
  have hhc : Continuous h := by
    have hs : Continuous sl := by rw [hsl_def]; fun_prop
    exact ((hVcont.comp hs).mul (Complex.continuous_conj.comp ((continuous_dirLock hP).comp hs))).sub
      (continuous_const.mul ((continuous_dirLock hP).comp hs))
  have hgood : ∀ y : ℝ, 0 < y → xi (sl y) ≠ 0 → h y = 0 := by
    intro y hy hxi
    have hre : 1 / 2 ≤ (sl y).re := le_of_eq (hsl_re y).symm
    set g := G (sl y) with hg
    have hFy := hF hre
    have hg0 : g ≠ 0 := by
      intro h0; rw [← hg, h0, zero_mul] at hFy
      exact hxi (by
        have := hFy.symm
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd h1 (mul_ne_zero two_ne_zero hG1)
        · exact h1)
    have hline : lineS (-y / 2) = sl y := by rw [lineS_eq, hsl_def]; push_cast; ring
    have hL := hlockV (-y / 2) (by linarith)
    rw [hline] at hL
    have hconj : conj (sl y) = 1 - sl y := by
      apply Complex.ext <;> simp [hsl_def]; norm_num
    have hGc' := G_conj hsl hid hGc hGd hG2 hre
    rw [hconj] at hGc'
    -- `conj g = V g`
    have hcg : conj g = V (sl y) * g := by rw [← hGc', hL]
    have hxr := conj_xi_of_re_eq_half (hsl_re y)
    have key : V (sl y) * g * conj (dirLock P (sl y)) = κ * (g * dirLock P (sl y)) := by
      rw [← hcg, ← map_mul, hFy, map_mul, map_mul, hxr, Complex.conj_ofNat, ← hκG]
      ring
    have : g * (V (sl y) * conj (dirLock P (sl y)) - κ * dirLock P (sl y)) = 0 := by
      linear_combination key
    exact (mul_eq_zero.mp this).resolve_left hg0
  have hall : ∀ y : ℝ, 0 < y → h y = 0 := by
    intro y0 hy0
    by_cases hxi : xi (sl y0) ≠ 0
    · exact hgood y0 hy0 hxi
    push Not at hxi
    have hcod := (mem_codiscreteWithin.mp xi_ne_zero_codiscrete) (sl y0) (Set.mem_univ _)
    rw [disjoint_principal_right] at hcod
    have hT : Tendsto sl (𝓝[≠] y0) (𝓝[≠] (sl y0)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hs : Continuous sl := by rw [hsl_def]; fun_prop
        exact hs.continuousAt.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        intro heq
        apply hy
        have := congrArg Complex.im heq
        simp [hsl_def] at this
        exact this
    have hev : ∀ᶠ y in 𝓝[≠] y0, h y = 0 := by
      filter_upwards [hT hcod, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hy0)] with y hy hpos
      apply hgood y hpos
      simpa using hy
    exact tendsto_nhds_unique (hhc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hev.mono fun y hy => hy.symm))
  -- the integral coefficients vanish
  have hP2 : ∀ k, 2 ≤ k → P k = 0 := fun k hk =>
    natCoeff_eq_zero_of_line_identity hP hρ hq hagg hκ (fun y hy => by
      have := hall y hy
      simp only [hh, hV, sl] at this
      exact sub_eq_zero.mp this) hk
  have hconst : ∀ s : ℂ, 1 / 2 ≤ s.re → G s * P 1 = 2 * G 1 * xi s := fun s hs => by
    rw [← dirLock_eq_coeff_one hP2 hs]; exact hF hs
  have hP1 : P 1 ≠ 0 := by
    intro h0
    have := hconst 2 (by norm_num)
    rw [h0, mul_zero] at this
    exact (mul_ne_zero (mul_ne_zero two_ne_zero hG1) xi_two_ne_zero) this.symm
  refine phase_lock_rigidity hsl hΦd hΦre hid hGc hGd hG2 (Y := 0) le_rfl one_ne_zero ?_
  intro y _
  have h1 := hconst (1 / 2 - (y : ℂ) * I) (by simp)
  have h2 := hconst (1 / 2 + (y : ℂ) * I) (by simp)
  have hx : xi (1 / 2 - (y : ℂ) * I) = xi (1 / 2 + (y : ℂ) * I) := by
    rw [← xi_one_sub (1 / 2 + (y : ℂ) * I)]; congr 1; ring
  rw [one_mul]
  apply mul_right_cancel₀ hP1
  rw [h1, h2, hx]

/-- **Almost-periodic locks whose rational resonances are integral force the true producer.** -/
theorem integer_resonant_lock_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹)
    (hρq : ∀ j (a b : ℕ), 0 < b → (b : ℝ) * ρ j ≠ a)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      (LSeries P (lineS τ - 1 / 2) + ∑' j, q j * (ρ j : ℂ) ^ (-(lineS τ - 1 / 2))) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis :=
  aggregated_resonant_lock_rigidity hsl hΦd hΦre hid hGc hGd hG2 hP hρ hq
    (fun a b hb => (tsum_congr fun j => if_neg (hρq j a b hb)).trans tsum_zero) hlock

end

end AbelianTwist

end RHTower
