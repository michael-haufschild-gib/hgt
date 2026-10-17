import GaloisForLFunctions.HTGeometry.SymbolicRuellePollicottBounds

/-!
# Splitting periodic-orbit sums into outer traces and small remainders

* `pow_sub_pow_eq_sum`, `norm_pow_sub_pow_le_of_exp_bound` — `aⁿ − bⁿ = Σ a^{n−1−i}(a − b)bⁱ`
  in any ring, and the resulting norm bound.
* `norm_outerTrace_sub_le` — outer traces of nearby operators are close:
  `|tr(T'ⁿ|_{W'}) − tr(Tⁿ|_W)| ≤ 2r (‖T'ⁿ − Tⁿ‖ + ρ^{n+1} 2Λ² ‖T' − T‖)`.
* `periodicOrbitSum_eq_outerTrace_add` — for an `m`-local potential whose outer spectral subspace
  lies in `V_{m−1}`, `Σ_{σⁿp=p} e^{−s ψⁿ(p)} = tr(Lⁿ|_W) + R_n` with `|R_n| ≤ k^m ρ^{n+1} Λ`: the
  periodic sum is the trace on `V_n`, and the part of `Lⁿ` inside the circle lives on `V_m`.
* `summable_pow_mul_pow_div` — `Σ_n n^a τ^{⌊n/q⌋} < ∞` for `τ < 1`.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Filter Topology FiniteRank Module

noncomputable section

/-- `aⁿ − bⁿ = Σ_{i<n} a^{n−1−i}(a − b)bⁱ`. -/
theorem pow_sub_pow_eq_sum {R : Type*} [Ring R] (a b : R) (n : ℕ) :
    a ^ n - b ^ n = ∑ i ∈ Finset.range n, a ^ (n - 1 - i) * (a - b) * b ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    have hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by
      rw [pow_succ', pow_succ']; noncomm_ring
    rw [hsplit, ih, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < n := Finset.mem_range.mp hi
    rw [← mul_assoc, ← mul_assoc, ← pow_succ']
    congr 3
    omega

/-- `‖aⁿ − bⁿ‖ ≤ n K² e^{(n−1)κ} ‖a − b‖` when all powers are bounded by `K e^{iκ}`. -/
theorem norm_pow_sub_pow_le_of_exp_bound {R : Type*} [NormedRing R] (a b : R) {K κ : ℝ}
    (hK : 0 ≤ K) (hκ : 0 ≤ κ) (ha : ∀ i : ℕ, ‖a ^ i‖ ≤ K * Real.exp (i * κ))
    (hb : ∀ i : ℕ, ‖b ^ i‖ ≤ K * Real.exp (i * κ)) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ n * K ^ 2 * Real.exp (n * κ) * ‖a - b‖ := by
  rw [pow_sub_pow_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ Finset.range n, ‖a ^ (n - 1 - i) * (a - b) * b ^ i‖
      ≤ ∑ _i ∈ Finset.range n, K ^ 2 * Real.exp (n * κ) * ‖a - b‖ := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i < n := Finset.mem_range.mp hi
        calc ‖a ^ (n - 1 - i) * (a - b) * b ^ i‖ ≤ ‖a ^ (n - 1 - i)‖ * ‖a - b‖ * ‖b ^ i‖ :=
              (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
                (norm_nonneg _))
          _ ≤ (K * Real.exp ((n - 1 - i : ℕ) * κ)) * ‖a - b‖ * (K * Real.exp (i * κ)) := by
              gcongr
              · exact ha _
              · exact hb _
          _ = K ^ 2 * Real.exp (((n - 1 - i : ℕ) + i : ℝ) * κ) * ‖a - b‖ := by
              rw [add_mul, Real.exp_add]; ring
          _ ≤ K ^ 2 * Real.exp (n * κ) * ‖a - b‖ := by
              gcongr
              have : ((n - 1 - i : ℕ) : ℝ) + i ≤ n := by
                have : n - 1 - i + i ≤ n := by omega
                exact_mod_cast this
              exact this
    _ = n * K ^ 2 * Real.exp (n * κ) * ‖a - b‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Outer traces of nearby operators are close.** -/
theorem norm_outerTrace_sub_le (T T' : E →L[ℂ] E) {ρ Λ : ℝ} (hρ : 0 < ρ)
    (h : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ T)
    (hΛ : ∀ w ∈ sphere (0 : ℂ) ρ, ‖resolvent T w‖ ≤ Λ) (hTT' : 2 * ‖T' - T‖ * Λ ≤ 1)
    {r : ℕ} [FiniteDimensional ℂ (opRange (outerProj T ρ))]
    [FiniteDimensional ℂ (opRange (outerProj T' ρ))]
    (hr : finrank ℂ (opRange (outerProj T ρ)) ≤ r) (hr' : finrank ℂ (opRange (outerProj T' ρ)) ≤ r)
    (n : ℕ) :
    ‖outerTrace T' ρ n - outerTrace T ρ n‖ ≤
      2 * r * (‖T' ^ n - T ^ n‖ + ρ ^ (n + 1) * (2 * Λ ^ 2 * ‖T' - T‖)) := by
  have h' : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ T' :=
    (resolvent_bound_of_perturb T T' h hΛ hTT').1
  set W := opRange (outerProj T ρ) ⊔ opRange (outerProj T' ρ)
  have hm : ∀ v, (T ^ n * outerProj T ρ) v ∈ W := fun v => by
    refine Submodule.mem_sup_left ?_
    rw [(Commute.pow_left (commute_outerProj hρ h) n).eq]; exact mem_opRange _ _
  have hm' : ∀ v, (T' ^ n * outerProj T' ρ) v ∈ W := fun v => by
    refine Submodule.mem_sup_right ?_
    rw [(Commute.pow_left (commute_outerProj hρ h') n).eq]; exact mem_opRange _ _
  have hdim : (finrank ℂ W : ℝ) ≤ 2 * r := by
    have h1 := Submodule.finrank_add_le_finrank_add_finrank (opRange (outerProj T ρ))
      (opRange (outerProj T' ρ))
    have h2 : finrank ℂ W ≤ 2 * r := le_trans h1 (by omega)
    exact_mod_cast h2
  rw [outerTrace, outerTrace, ← finiteRankTrace_sub_of_le _ _ W hm' hm]
  refine (norm_finiteRankTrace_le _ W fun v => W.sub_mem (hm' v) (hm v)).trans ?_
  have hdiff : T' ^ n * outerProj T' ρ - T ^ n * outerProj T ρ =
      (T' ^ n - T ^ n) - (T' ^ n * rieszProjection T' 0 ρ - T ^ n * rieszProjection T 0 ρ) := by
    simp only [outerProj, mul_sub, mul_one]; abel
  rw [hdiff]
  have hP := norm_pow_mul_rieszProjection_sub_le T T' hρ.le h hΛ hTT' n
  calc (finrank ℂ W : ℝ) * ‖(T' ^ n - T ^ n) -
        (T' ^ n * rieszProjection T' 0 ρ - T ^ n * rieszProjection T 0 ρ)‖
      ≤ 2 * r * (‖T' ^ n - T ^ n‖ + ρ ^ (n + 1) * (2 * Λ ^ 2 * ‖T' - T‖)) := by
        refine mul_le_mul hdim ((norm_sub_le _ _).trans (add_le_add le_rfl hP))
          (norm_nonneg _) (by positivity)

end Abstract

/-- `Σ_n n^a τ^{⌊n/q⌋} < ∞` for `0 ≤ τ < 1` and `q ≥ 1`. -/
theorem summable_pow_mul_pow_div {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) {q : ℕ} (hq : 1 ≤ q)
    (a : ℕ) : Summable fun n : ℕ => (n : ℝ) ^ a * τ ^ (n / q) := by
  set τ' := max τ (1 / 2)
  have hτ'0 : 0 < τ' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hτ'1 : τ' < 1 := max_lt hτ1 (by norm_num)
  set ν := τ' ^ ((q : ℝ)⁻¹)
  have hν0 : 0 < ν := Real.rpow_pos_of_pos hτ'0 _
  have hν1 : ν < 1 := Real.rpow_lt_one hτ'0.le hτ'1 (by positivity)
  have hνq : ν ^ q = τ' := Real.rpow_inv_natCast_pow hτ'0.le (by omega)
  have hbound : ∀ n : ℕ, τ ^ (n / q) ≤ (ν ^ (q - 1))⁻¹ * ν ^ n := by
    intro n
    have e1 : τ ^ (n / q) ≤ τ' ^ (n / q) := pow_le_pow_left₀ hτ0 (le_max_left _ _) _
    have e2 : τ' ^ (n / q) = ν ^ (q * (n / q)) := by rw [pow_mul, hνq]
    have e3 : n ≤ q * (n / q) + (q - 1) := by
      have := Nat.lt_div_mul_add (a := n) (b := q) (by omega)
      rw [mul_comm]; omega
    have e4 : ν ^ (q * (n / q) + (q - 1)) ≤ ν ^ n := pow_le_pow_of_le_one hν0.le hν1.le e3
    rw [pow_add] at e4
    calc τ ^ (n / q) ≤ ν ^ (q * (n / q)) := e1.trans e2.le
      _ ≤ (ν ^ (q - 1))⁻¹ * ν ^ n := by
          rw [le_inv_mul_iff₀ (pow_pos hν0 _), mul_comm]; exact e4
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_pow_mul_geometric_of_norm_lt_one a (r := ν)
      (by rw [Real.norm_eq_abs, abs_of_pos hν0]; exact hν1)).mul_left (ν ^ (q - 1))⁻¹)
  calc (n : ℝ) ^ a * τ ^ (n / q) ≤ (n : ℝ) ^ a * ((ν ^ (q - 1))⁻¹ * ν ^ n) :=
        mul_le_mul_of_nonneg_left (hbound n) (by positivity)
    _ = (ν ^ (q - 1))⁻¹ * ((n : ℝ) ^ a * ν ^ n) := by ring

namespace Symbolic

variable {k : ℕ} {A : Fin k → Fin k → Prop} {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1)
  {ψ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ} (hψ : IsHolderPotential A ψ R₀ C θ) (hC : 0 ≤ C)
  (hθ0 : 0 ≤ θ) (hθϑ : θ ≤ ϑ) (hθ1 : θ < 1)

/-- **Periodic sums are outer traces up to a small remainder.**  For an `m`-local potential with
outer spectral subspace inside `V_{m−1}`,
`Σ_{σⁿp=p} e^{−s ψⁿ(p)} = tr(Lⁿ|_W) + R` with `|R| ≤ k^m ρ^{n+1} Λ`. -/
theorem periodicSum_eq_outerTrace_add {m : ℕ} (hloc : IsLocal A ψ m) (hm : 2 ≤ m) (s : ℂ)
    {ρ Λ : ℝ} (hρ : 0 < ρ)
    (h : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ (transferOp hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s))
    (hΛ : ∀ w ∈ sphere (0 : ℂ) ρ,
      ‖resolvent (transferOp hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s) w‖ ≤ Λ)
    (hQ : ∀ v, outerProj (transferOp hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s) ρ v ∈ levelSpace A ϑ (m - 1))
    {n : ℕ} [NeZero n] (hmn : m ≤ n + 1) :
    ∃ R : ℂ, (∑ p ∈ periodicPoints A n, Complex.exp (-(s * birkhoff ψ n p))) =
      outerTrace (transferOp hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s) ρ n + R ∧
      ‖R‖ ≤ k ^ m * (ρ ^ (n + 1) * Λ) := by
  set T := transferOp hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s
  set P := rieszProjection T 0 ρ
  set Q := outerProj T ρ
  set E := cylAverage (A := A) hϑ n
  set Vn := levelSpace A ϑ n
  have hle1 : levelSpace A ϑ (m - 1) ≤ Vn := levelSpace_mono (by omega)
  have hle2 : levelSpace A ϑ (m - 1) ≤ levelSpace A ϑ m := levelSpace_mono (by omega)
  have hTE : ∀ v, (T ^ n * E) v ∈ levelSpace A ϑ (m - 1) := by
    intro v
    have := transferOp_pow_mem_levelSpace hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 hloc hm s n
      (cylAverage_mem hϑ n v)
    rwa [Nat.sub_self, Nat.max_zero] at this
  have hTQ : ∀ v, (T ^ n * Q) v ∈ levelSpace A ϑ (m - 1) := by
    intro v
    rw [(Commute.pow_left (commute_outerProj hρ h) n).eq]
    exact hQ _
  have hTQE : ∀ v, (T ^ n * Q * E) v ∈ levelSpace A ϑ (m - 1) := fun v => hTQ (E v)
  have hTPE_eq : T ^ n * P * E = T ^ n * E - T ^ n * Q * E := by
    simp only [Q, outerProj, P, mul_sub, sub_mul, mul_one]; abel
  have hTPE : ∀ v, (T ^ n * P * E) v ∈ levelSpace A ϑ (m - 1) := by
    intro v
    rw [hTPE_eq]
    exact Submodule.sub_mem _ (hTE v) (hTQE v)
  have hEfix : ∀ w ∈ Vn, E w = w := fun w hw => cylAverage_of_mem hϑ hw
  refine ⟨finiteRankTrace (T ^ n * P * E), ?_, ?_⟩
  · -- the periodic sum is the trace of `Tⁿ E` on `V_n`
    have hinv := transferOp_pow_levelSpace_invariant hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 hloc
      (NeZero.one_le) hmn s
    have hsum := trace_transferOp_pow_levelSpace hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 hloc hmn s
    have e1 : finiteRankTrace (T ^ n * E) = LinearMap.trace ℂ Vn
        (restrictEnd (T ^ n) Vn hinv) := by
      rw [finiteRankTrace_eq_trace_restrict _ Vn fun v => hle1 (hTE v)]
      congr 1
      refine LinearMap.ext fun w => Subtype.ext ?_
      rw [coe_restrictEnd_apply, coe_restrictEnd_apply]
      show (T ^ n) (E w) = _
      rw [hEfix _ w.2]
    have e2 : finiteRankTrace (T ^ n * Q * E) = outerTrace T ρ n := by
      rw [outerTrace, finiteRankTrace_eq_trace_restrict _ Vn fun v => hle1 (hTQE v),
        finiteRankTrace_eq_trace_restrict _ Vn fun v => hle1 (hTQ v)]
      congr 1
      refine LinearMap.ext fun w => Subtype.ext ?_
      rw [coe_restrictEnd_apply, coe_restrictEnd_apply]
      show (T ^ n * Q) (E w) = _
      rw [hEfix _ w.2]
    have hsplit : T ^ n * E = T ^ n * Q * E + T ^ n * P * E := by
      rw [hTPE_eq]; abel
    rw [← hsum, ← e1, hsplit, finiteRankTrace_add_of_le _ _ Vn (fun v => hle1 (hTQE v))
      (fun v => hle1 (hTPE v)), e2]
  · haveI : FiniteDimensional ℂ (levelSpace A ϑ m) := inferInstance
    refine (norm_finiteRankTrace_le _ (levelSpace A ϑ m) fun v => hle2 (hTPE v)).trans ?_
    have hfr : (finrank ℂ (levelSpace A ϑ m) : ℝ) ≤ k ^ m := by
      exact_mod_cast finrank_levelSpace_le m
    have hnorm : ‖T ^ n * P * E‖ ≤ ρ ^ (n + 1) * Λ := by
      refine (norm_mul_le _ _).trans ?_
      have hE : ‖E‖ ≤ 1 := norm_cylAverage_le hϑ n
      calc ‖T ^ n * P‖ * ‖E‖ ≤ ρ ^ (n + 1) * Λ * 1 :=
            mul_le_mul (norm_pow_mul_rieszProjection_le T hρ.le h hΛ n) hE (norm_nonneg _)
              (by have := (norm_nonneg (resolvent T ρ)).trans (hΛ ρ (by simp [abs_of_pos hρ]))
                  positivity)
        _ = ρ ^ (n + 1) * Λ := mul_one _
    exact mul_le_mul hfr hnorm (norm_nonneg _) (by positivity)

end Symbolic

end

end GaloisForLFunctions.HTGeometry
