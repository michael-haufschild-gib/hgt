import GaloisForLFunctions.PrimeTorusTheory.TheHullOverTheTorus

/-!
# Prime characters are lacunary

The characters `x_p`, `p` prime, on the gauge torus behave like a lacunary system: by unique factorization the products `x_p conj x_q`, `p ≠ q`, are orthonormal (`integral_pairChar_mul_conj`). So a set of positive measure correlates with few of them.

**Bessel** (`sum_norm_corr_sq_le`). `Σ_{p≠q} |∫_E x_p conj x_q|² ≤ |E|`, so the tail beyond some `P` is as small as we like (`exists_tail_corr_small`).

**The off-diagonal** (`le_setIntegral_normSq`). If that tail is at most `τ²`, then `(|E| − τ) Σ_{P≤p} |a_p|² ≤ ∫_E |Σ_{P≤p} a_p x_p|²`.

**Zygmund's theorem on the torus** (`measure_bounded_prime_sums_eq_zero`). Let `Re s_j ↓ ½`. The prime sums `g_j = Σ_p p^{−s_j} x_p`, perturbed by anything bounded in `L²` uniformly in `j`, are bounded on a set of measure zero only. A bound on a set `E` of positive measure would give `(|E|/2) Σ_{P≤p} p^{−2σ_j} = O(1)` uniformly in `j`, and `Σ 1/p = ∞`.
-/

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.PrimeTorusTheory

open ArithmeticCorrelationGeometry

noncomputable section

local notation "conj" => starRingEnd ℂ

/-- The character `x_p conj x_q`. -/
def pairChar (p q : ℕ) (x : GaugeTorus) : ℂ := twist x p * conj (twist x q)

theorem continuous_pairChar (p q : ℕ) : Continuous (pairChar p q) := by
  unfold pairChar
  exact (continuous_twist p).mul (Complex.continuous_conj.comp (continuous_twist q))

theorem norm_pairChar (p q : ℕ) (x : GaugeTorus) : ‖pairChar p q x‖ = 1 := by
  unfold pairChar
  rw [norm_mul, Complex.norm_conj, norm_twist, norm_twist, one_mul]

theorem pairChar_self (p : ℕ) (x : GaugeTorus) : pairChar p p x = 1 := twist_mul_conj_self x p

/-- Unique factorization makes the pair characters orthonormal. -/
theorem integral_pairChar_mul_conj {p q p' q' : ℕ} (hp : p.Prime) (hq : q.Prime) (hp' : p'.Prime)
    (hq' : q'.Prime) (hne : p ≠ q) :
    ∫ x, pairChar p q x * conj (pairChar p' q' x) ∂gaugeHaar =
      if (p, q) = (p', q') then 1 else 0 := by
  have e : ∀ x : GaugeTorus, pairChar p q x * conj (pairChar p' q' x) =
      twist x (p * q') * conj (twist x (q * p')) := by
    intro x
    unfold pairChar
    rw [twist_mul x hp.ne_zero hq'.ne_zero, twist_mul x hq.ne_zero hp'.ne_zero]
    simp only [map_mul, Complex.conj_conj]
    ring
  simp_rw [e]
  rw [integral_twist_mul_conj (Nat.mul_ne_zero hp.ne_zero hq'.ne_zero)
    (Nat.mul_ne_zero hq.ne_zero hp'.ne_zero)]
  congr 1
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : p ∣ q * p' := Dvd.intro _ h
    have h2 : p = p' := by
      rcases (Nat.Prime.dvd_mul hp).mp h1 with h3 | h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp h3) hne
      · exact (Nat.prime_dvd_prime_iff_eq hp hp').mp h3
    subst h2
    have h3 : q' = q := by
      have := Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h]; ring : p * q' = p * q)
      exact this
    rw [h3]
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    rw [h1, h2]
    ring

variable {E : Set GaugeTorus}

/-- The correlation of a set with a pair character. -/
def corr (E : Set GaugeTorus) (α : ℕ × ℕ) : ℂ := ∫ x in E, pairChar α.1 α.2 x ∂gaugeHaar

theorem integrable_of_continuous_torus {F : Type*} [NormedAddCommGroup F] {f : GaugeTorus → F}
    (hf : Continuous f) : Integrable f gaugeHaar := by
  obtain ⟨C, hC⟩ := isCompact_range hf |>.isBounded.exists_norm_le
  exact Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun x => hC _ ⟨x, rfl⟩)

/-- **Bessel.** The correlations of a set with the pair characters have square sum at most its measure. -/
theorem sum_norm_corr_sq_le (T : Finset (ℕ × ℕ))
    (hT : ∀ α ∈ T, α.1.Prime ∧ α.2.Prime ∧ α.1 ≠ α.2) :
    ∑ α ∈ T, ‖corr E α‖ ^ 2 ≤ (gaugeHaar E).toReal := by
  classical
  set k : GaugeTorus → ℂ := fun x => ∑ β ∈ T, conj (corr E β) * pairChar β.1 β.2 x with hk
  have hkc : Continuous k := continuous_finsetSum _ fun β _ =>
    continuous_const.mul (continuous_pairChar β.1 β.2)
  set A : ℝ := ∑ α ∈ T, ‖corr E α‖ ^ 2 with hA
  have hint : ∀ β : ℕ × ℕ, Integrable (fun x => conj (corr E β) * pairChar β.1 β.2 x) gaugeHaar := fun β =>
    integrable_of_continuous_torus (continuous_const.mul (continuous_pairChar β.1 β.2))
  -- The set integral of `k` is `A`.
  have hEk : ∫ x in E, k x ∂gaugeHaar = (A : ℂ) := by
    simp only [hk]
    rw [integral_finsetSum _ fun β _ => (hint β).integrableOn]
    rw [hA]
    push_cast
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [integral_const_mul]
    change conj (corr E β) * corr E β = _
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  -- The full integral of `|k|²` is `A`.
  have hfull : ∫ x, ‖k x‖ ^ 2 ∂gaugeHaar = A := by
    have hexp : ∀ x, ((‖k x‖ ^ 2 : ℝ) : ℂ) = ∑ β ∈ T, ∑ γ ∈ T,
        conj (corr E β) * corr E γ * (pairChar β.1 β.2 x * conj (pairChar γ.1 γ.2 x)) := by
      intro x
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
      simp only [hk, map_sum, map_mul, Complex.conj_conj]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun γ _ => ?_
      ring
    have hc : ((∫ x, ‖k x‖ ^ 2 ∂gaugeHaar : ℝ) : ℂ) = (A : ℂ) := by
      rw [← integral_complex_ofReal]
      simp_rw [hexp]
      have hi : ∀ β γ : ℕ × ℕ, Integrable (fun x => conj (corr E β) * corr E γ *
          (pairChar β.1 β.2 x * conj (pairChar γ.1 γ.2 x))) gaugeHaar := fun β γ =>
        integrable_of_continuous_torus (continuous_const.mul ((continuous_pairChar β.1 β.2).mul
          (Complex.continuous_conj.comp (continuous_pairChar γ.1 γ.2))))
      rw [integral_finsetSum _ fun β _ => integrable_finsetSum _ fun γ _ => hi β γ]
      rw [hA]
      push_cast
      refine Finset.sum_congr rfl fun β hβ => ?_
      rw [integral_finsetSum _ fun γ _ => hi β γ]
      obtain ⟨h1, h2, h3⟩ := hT β hβ
      have hterm : ∀ γ ∈ T, ∫ x, conj (corr E β) * corr E γ *
          (pairChar β.1 β.2 x * conj (pairChar γ.1 γ.2 x)) ∂gaugeHaar =
          if γ = β then conj (corr E β) * corr E γ else 0 := by
        intro γ hγ
        obtain ⟨h4, h5, -⟩ := hT γ hγ
        rw [integral_const_mul, integral_pairChar_mul_conj h1 h2 h4 h5 h3]
        by_cases hc : γ = β
        · simp [hc]
        · have : (β.1, β.2) ≠ (γ.1, γ.2) := fun h => hc (Prod.ext (Prod.mk.inj h).1.symm (Prod.mk.inj h).2.symm)
          simp [hc, this]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' T β, if_pos hβ, mul_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    exact_mod_cast hc
  -- `|k|² ≥ 2 Re k − 1` on `E`.
  have hint2 : Integrable (fun x => ‖k x‖ ^ 2) gaugeHaar := by
    have : Continuous fun x => ‖k x‖ ^ 2 := hkc.norm.pow 2
    obtain ⟨C, hC⟩ := isCompact_range this |>.isBounded.exists_norm_le
    exact Integrable.of_bound this.aestronglyMeasurable C (Eventually.of_forall fun x => hC _ ⟨x, rfl⟩)
  have hset : ∫ x in E, ‖k x‖ ^ 2 ∂gaugeHaar ≤ A := by
    rw [← hfull]
    exact setIntegral_le_integral hint2 (Eventually.of_forall fun x => by positivity)
  have hint3 : Integrable (fun x => (k x).re) gaugeHaar :=
    integrable_of_continuous_torus hkc |>.re
  have hre : ∫ x in E, (k x).re ∂gaugeHaar = A := by
    have h1 : ∫ x in E, (k x).re ∂gaugeHaar = (∫ x in E, k x ∂gaugeHaar).re :=
      Complex.reCLM.integral_comp_comm (integrable_of_continuous_torus hkc).integrableOn
    rw [h1, hEk, Complex.ofReal_re]
  have h2 : Integrable (fun x => 2 * (k x).re - 1) gaugeHaar := (hint3.const_mul 2).sub (integrable_const 1)
  have hmono : ∫ x in E, (2 * (k x).re - 1) ∂gaugeHaar ≤ ∫ x in E, ‖k x‖ ^ 2 ∂gaugeHaar := by
    refine setIntegral_mono h2.integrableOn hint2.integrableOn fun x => ?_
    have h3 : ‖k x‖ ^ 2 = (k x).re ^ 2 + (k x).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    simp only
    nlinarith [sq_nonneg ((k x).re - 1), sq_nonneg (k x).im]
  have hval : ∫ x in E, (2 * (k x).re - 1) ∂gaugeHaar = 2 * A - (gaugeHaar E).toReal := by
    rw [integral_sub (hint3.const_mul 2).integrableOn (integrable_const 1).integrableOn,
      integral_const_mul, hre, setIntegral_const]
    simp [Measure.real]
  linarith

/-- **The off-diagonal is small.** If the correlations of `E` with the pair characters of `Ps` have square sum at most `τ²`, then `∫_E |Σ a_p x_p|² ≥ (|E| − τ) Σ |a_p|²`. -/
theorem le_setIntegral_normSq (Ps : Finset ℕ) (a : ℕ → ℂ) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ : ∑ α ∈ Ps.offDiag, ‖corr E α‖ ^ 2 ≤ τ ^ 2) :
    ((gaugeHaar E).toReal - τ) * ∑ p ∈ Ps, ‖a p‖ ^ 2 ≤
      ∫ x in E, ‖∑ p ∈ Ps, a p * twist x p‖ ^ 2 ∂gaugeHaar := by
  classical
  set A : ℝ := ∑ p ∈ Ps, ‖a p‖ ^ 2 with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => by positivity
  have hexp : ∀ x : GaugeTorus, ((‖∑ p ∈ Ps, a p * twist x p‖ ^ 2 : ℝ) : ℂ) =
      ∑ α ∈ Ps ×ˢ Ps, a α.1 * conj (a α.2) * pairChar α.1 α.2 x := by
    intro x
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum,
      Finset.sum_product]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    unfold pairChar
    simp only [map_mul]
    ring
  have hi : ∀ α : ℕ × ℕ, Integrable (fun x => a α.1 * conj (a α.2) * pairChar α.1 α.2 x) gaugeHaar := fun α =>
    integrable_of_continuous_torus (continuous_const.mul (continuous_pairChar α.1 α.2))
  have hset : ((∫ x in E, ‖∑ p ∈ Ps, a p * twist x p‖ ^ 2 ∂gaugeHaar : ℝ) : ℂ) =
      ∑ α ∈ Ps ×ˢ Ps, a α.1 * conj (a α.2) * corr E α := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun α _ => (hi α).integrableOn]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_const_mul]
    rfl
  -- Split into the diagonal and the rest.
  rw [← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag _)] at hset
  have hdiag : ∑ α ∈ Ps.diag, a α.1 * conj (a α.2) * corr E α =
      ((A * (gaugeHaar E).toReal : ℝ) : ℂ) := by
    rw [Finset.sum_diag, hA]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hc : corr E (p, p) = ((gaugeHaar E).toReal : ℂ) := by
      unfold corr
      simp only [pairChar_self]
      rw [setIntegral_const]
      simp [Measure.real]
    rw [hc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  -- The off-diagonal, by Cauchy–Schwarz.
  set O : ℂ := ∑ α ∈ Ps.offDiag, a α.1 * conj (a α.2) * corr E α with hO
  have hOnorm : ‖O‖ ≤ A * τ := by
    have h1 : ‖O‖ ≤ ∑ α ∈ Ps.offDiag, (‖a α.1‖ * ‖a α.2‖) * ‖corr E α‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_conj]
    have h2 : (∑ α ∈ Ps.offDiag, (‖a α.1‖ * ‖a α.2‖) * ‖corr E α‖) ^ 2 ≤
        (∑ α ∈ Ps.offDiag, (‖a α.1‖ * ‖a α.2‖) ^ 2) * ∑ α ∈ Ps.offDiag, ‖corr E α‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : ∑ α ∈ Ps.offDiag, (‖a α.1‖ * ‖a α.2‖) ^ 2 ≤ A ^ 2 := by
      have hsub : Ps.offDiag ⊆ Ps ×ˢ Ps := fun α hα =>
        Finset.mem_product.mpr ⟨(Finset.mem_offDiag.mp hα).1, (Finset.mem_offDiag.mp hα).2.1⟩
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans (le_of_eq ?_)
      rw [Finset.sum_product, hA, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    have h4 : (∑ α ∈ Ps.offDiag, (‖a α.1‖ * ‖a α.2‖) * ‖corr E α‖) ^ 2 ≤ (A * τ) ^ 2 := by
      refine h2.trans ?_
      rw [mul_pow]
      exact mul_le_mul h3 hτ (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    have h5 := abs_le_of_sq_le_sq' h4 (by positivity)
    exact h1.trans h5.2
  have hre := congrArg Complex.re hset
  rw [Complex.ofReal_re, Complex.add_re, hdiag, Complex.ofReal_re] at hre
  rw [hre]
  have h6 := Complex.abs_re_le_norm O
  have h7 : -(A * τ) ≤ O.re := by
    have := (abs_le.mp (h6.trans hOnorm)).1
    linarith
  nlinarith

/-- **Fatou for orthogonal sums.** The a.e. limit of partial sums has square integral at most the bound on the coefficient sums. -/
theorem lintegral_normSq_limit_le {s : ℕ → Finset ℕ} (hs : ∀ N, ∀ n ∈ s N, n ≠ 0) (a : ℕ → ℂ) {B : ℝ}
    (hB : ∀ N, ∑ n ∈ s N, ‖a n‖ ^ 2 ≤ B) {g : GaugeTorus → ℂ}
    (hg : ∀ᵐ x ∂gaugeHaar, Tendsto (fun N => twistSum (s N) a x) atTop (𝓝 (g x))) :
    ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂gaugeHaar ≤ ENNReal.ofReal B := by
  set f : ℕ → GaugeTorus → ENNReal := fun N x => ENNReal.ofReal (‖twistSum (s N) a x‖ ^ 2) with hf
  have hcont : ∀ N, Continuous fun x => ‖twistSum (s N) a x‖ ^ 2 := fun N =>
    (continuous_twistSum (s N) a).norm.pow 2
  have hmeas : ∀ N, Measurable (f N) := fun N => ENNReal.measurable_ofReal.comp (hcont N).measurable
  have hae : (fun x => ENNReal.ofReal (‖g x‖ ^ 2)) =ᵐ[gaugeHaar] fun x => liminf (fun N => f N x) atTop := by
    filter_upwards [hg] with x hx
    have h1 : Tendsto (fun N => f N x) atTop (𝓝 (ENNReal.ofReal (‖g x‖ ^ 2))) :=
      ENNReal.tendsto_ofReal (hx.norm.pow 2)
    exact h1.liminf_eq.symm
  rw [lintegral_congr_ae hae]
  refine (lintegral_liminf_le hmeas).trans ?_
  refine liminf_le_of_frequently_le' (Frequently.of_forall fun N => ?_)
  have hint : Integrable (fun x => ‖twistSum (s N) a x‖ ^ 2) gaugeHaar := by
    obtain ⟨C, hC⟩ := isCompact_range (hcont N) |>.isBounded.exists_norm_le
    exact Integrable.of_bound (hcont N).aestronglyMeasurable C (Eventually.of_forall fun x => hC _ ⟨x, rfl⟩)
  rw [show (∫⁻ x, f N x ∂gaugeHaar) = ENNReal.ofReal (∫ x, ‖twistSum (s N) a x‖ ^ 2 ∂gaugeHaar) from
    (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity)).symm,
    integral_normSq_twistSum (hs N) a]
  exact ENNReal.ofReal_le_ofReal (hB N)

/-! ### The tail of the correlations -/

/-- The correlations of a set with the pair characters of large primes are small in square sum. -/
theorem exists_tail_corr_small (E : Set GaugeTorus) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℕ, ∀ Ps : Finset ℕ, (∀ p ∈ Ps, p.Prime ∧ P ≤ p) → ∑ α ∈ Ps.offDiag, ‖corr E α‖ ^ 2 ≤ ε := by
  classical
  set f : ℕ × ℕ → ℝ := fun α => if α.1.Prime ∧ α.2.Prime ∧ α.1 ≠ α.2 then ‖corr E α‖ ^ 2 else 0 with hf
  have hf0 : ∀ α, 0 ≤ f α := fun α => by
    simp only [hf]
    split_ifs
    · positivity
    · exact le_rfl
  have hsum : Summable f := by
    refine summable_of_sum_le hf0 (c := (gaugeHaar E).toReal) fun u => ?_
    have h1 : ∑ α ∈ u, f α = ∑ α ∈ u.filter fun α => α.1.Prime ∧ α.2.Prime ∧ α.1 ≠ α.2, ‖corr E α‖ ^ 2 := by
      rw [Finset.sum_filter]
    rw [h1]
    exact sum_norm_corr_sq_le _ fun α hα => (Finset.mem_filter.mp hα).2
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hsum ε hε
  refine ⟨s.sup (fun α => α.1) + 1, fun Ps hPs => ?_⟩
  have hdisj : Disjoint Ps.offDiag s := by
    rw [Finset.disjoint_left]
    intro α hα hαs
    have h1 := (Finset.mem_offDiag.mp hα).1
    have h2 := (hPs _ h1).2
    have h3 : α.1 ≤ s.sup (fun α => α.1) := Finset.le_sup (f := fun α : ℕ × ℕ => α.1) hαs
    omega
  have h := hs _ hdisj
  have h1 : ∑ α ∈ Ps.offDiag, f α = ∑ α ∈ Ps.offDiag, ‖corr E α‖ ^ 2 := by
    refine Finset.sum_congr rfl fun α hα => ?_
    obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hα
    simp only [hf]
    rw [if_pos ⟨(hPs _ h1).1, (hPs _ h2).1, h3⟩]
  rw [h1, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)] at h
  exact h.le

/-! ### The prime sums -/

/-- The coefficient `n^{−s}`. -/
def powCoeff (s : ℂ) (n : ℕ) : ℂ := (n : ℂ) ^ (-s)

/-- The partial sum `Σ_{p<N} x_p p^{−s}`. -/
def primeSum (N : ℕ) (s : ℂ) (x : GaugeTorus) : ℂ := twistSum N.primesBelow (powCoeff s) x

theorem norm_powCoeff_sq {p : ℕ} (hp : 0 < p) (s : ℂ) :
    ‖powCoeff s p‖ ^ 2 = (p : ℝ) ^ (-(2 * s.re)) := by
  unfold powCoeff
  rw [Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg p)]
  congr 1
  push_cast
  ring

theorem primesBelow_subset {P N : ℕ} (h : P ≤ N) : P.primesBelow ⊆ N.primesBelow := fun p hp => by
  obtain ⟨h1, h2⟩ := Nat.mem_primesBelow.mp hp
  exact Nat.mem_primesBelow.mpr ⟨h1.trans_le h, h2⟩

/-- A sum over all primes is the limit of the sums over `primesBelow`. -/
theorem tendsto_sum_primesBelow {F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {g : ℕ → F}
    (h : Summable fun p : Nat.Primes => g p) :
    Tendsto (fun N : ℕ => ∑ p ∈ N.primesBelow, g p) atTop (𝓝 (∑' p : Nat.Primes, g p)) := by
  classical
  have h1 := h.hasSum
  have h2 : HasSum ({p : ℕ | p.Prime}.indicator g) (∑' p : Nat.Primes, g p) :=
    hasSum_subtype_iff_indicator.mp h1
  refine h2.tendsto_sum_nat.congr fun N => ?_
  unfold Nat.primesBelow
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : n.Prime
  · simp [hn]
  · simp [hn]

/-- The square integral of the remainder of a prime sum. -/
theorem lintegral_sub_primeSum_le {s : ℂ} {T : ℝ} (hT : ∀ N : ℕ, ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-(2 * s.re)) ≤ T)
    {g : GaugeTorus → ℂ} (hg : ∀ᵐ x ∂gaugeHaar, Tendsto (fun N => primeSum N s x) atTop (𝓝 (g x))) (N : ℕ) :
    ∫⁻ x, ENNReal.ofReal (‖g x - primeSum N s x‖ ^ 2) ∂gaugeHaar ≤
      ENNReal.ofReal (T - ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-(2 * s.re))) := by
  classical
  have hsub : ∀ K, N.primesBelow ⊆ (N + K).primesBelow := fun K => primesBelow_subset (by omega)
  refine lintegral_normSq_limit_le (s := fun K => (N + K).primesBelow \ N.primesBelow) (a := powCoeff s)
    (fun K n hn => (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hn).1).2.ne_zero) (fun K => ?_) ?_
  · have h1 : ∑ n ∈ (N + K).primesBelow \ N.primesBelow, ‖powCoeff s n‖ ^ 2 =
        ∑ n ∈ (N + K).primesBelow, ‖powCoeff s n‖ ^ 2 - ∑ n ∈ N.primesBelow, ‖powCoeff s n‖ ^ 2 := by
      rw [← Finset.sum_sdiff (hsub K)]
      ring
    have h2 : ∀ L : ℕ, ∑ n ∈ L.primesBelow, ‖powCoeff s n‖ ^ 2 = ∑ p ∈ L.primesBelow, (p : ℝ) ^ (-(2 * s.re)) :=
      fun L => Finset.sum_congr rfl fun p hp => norm_powCoeff_sq (Nat.mem_primesBelow.mp hp).2.pos s
    rw [h1, h2, h2]
    linarith [hT (N + K)]
  · filter_upwards [hg] with x hx
    have h1 : Tendsto (fun K => primeSum (K + N) s x) atTop (𝓝 (g x)) :=
      (tendsto_add_atTop_iff_nat N).mpr hx
    have h2 := h1.sub_const (primeSum N s x)
    refine h2.congr fun K => ?_
    unfold primeSum twistSum
    rw [add_comm K N, ← Finset.sum_sdiff (hsub K)]
    ring

theorem sum_primesBelow_le_tsum {g : ℕ → ℝ} (hg : ∀ p, 0 ≤ g p)
    (h : Summable fun p : Nat.Primes => g p) (N : ℕ) :
    ∑ p ∈ N.primesBelow, g p ≤ ∑' p : Nat.Primes, g p := by
  have hm : Monotone fun N : ℕ => ∑ p ∈ N.primesBelow, g p := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (primesBelow_subset hab) fun p _ _ => hg p
  exact hm.ge_of_tendsto (tendsto_sum_primesBelow h) N

theorem continuous_primeSum (N : ℕ) (s : ℂ) : Continuous (primeSum N s) :=
  continuous_twistSum _ _

theorem norm_primeSum_le (P : ℕ) {s : ℂ} (hs : 0 < s.re) (x : GaugeTorus) :
    ‖primeSum P s x‖ ≤ (P.primesBelow.card : ℝ) := by
  unfold primeSum twistSum
  have h : ∀ p ∈ P.primesBelow, ‖powCoeff s p * twist x p‖ ≤ 1 := by
    intro p hp
    have hp' := (Nat.mem_primesBelow.mp hp).2
    rw [norm_mul, norm_twist, mul_one]
    unfold powCoeff
    rw [Complex.norm_natCast_cpow_of_pos hp'.pos, Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp'.one_lt.le) (by linarith)
  calc
    ‖∑ p ∈ P.primesBelow, powCoeff s p * twist x p‖ ≤ ∑ _p ∈ P.primesBelow, (1 : ℝ) :=
      norm_sum_le_of_le _ h
    _ = (P.primesBelow.card : ℝ) := by simp

theorem norm_sub_sub_sub_sq_le (a b c d : ℂ) :
    ‖a - b - c - d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h : ‖a - b - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    calc
      ‖a - b - c - d‖ ≤ ‖a - b - c‖ + ‖d‖ := norm_sub_le _ _
      _ ≤ ‖a - b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_sub_le _ _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖a‖ - ‖d‖),
    sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖b‖ - ‖d‖), sq_nonneg (‖c‖ - ‖d‖)]

/-- The set integral of a function dominated by two functions bounded in `L¹`, and a constant. -/
theorem setLIntegral_ofReal_le {f r e : GaugeTorus → ℝ} {c B₁ B₂ : ℝ}
    (hc : 0 ≤ c) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hr0 : ∀ x, 0 ≤ r x) (he0 : ∀ x, 0 ≤ e x)
    (hrm : AEMeasurable r gaugeHaar)
    (hf : ∀ᵐ x ∂gaugeHaar.restrict E, f x ≤ 4 * r x + 4 * e x + c)
    (hr : ∫⁻ x, ENNReal.ofReal (r x) ∂gaugeHaar ≤ ENNReal.ofReal B₁)
    (he : ∫⁻ x, ENNReal.ofReal (e x) ∂gaugeHaar ≤ ENNReal.ofReal B₂) :
    ∫⁻ x in E, ENNReal.ofReal (f x) ∂gaugeHaar ≤ ENNReal.ofReal (4 * B₁ + 4 * B₂ + c) := by
  have h4 : ENNReal.ofReal 4 ≠ ⊤ := ENNReal.ofReal_ne_top
  have hE1 : gaugeHaar E ≤ 1 := prob_le_one
  calc
    ∫⁻ x in E, ENNReal.ofReal (f x) ∂gaugeHaar
        ≤ ∫⁻ x in E, (ENNReal.ofReal 4 * ENNReal.ofReal (r x) + ENNReal.ofReal 4 * ENNReal.ofReal (e x) +
            ENNReal.ofReal c) ∂gaugeHaar := by
          refine lintegral_mono_ae ?_
          filter_upwards [hf] with x hx
          have hr1 := hr0 x
          have he1 := he0 x
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) hc]
          exact ENNReal.ofReal_le_ofReal hx
    _ = ∫⁻ x in E, (ENNReal.ofReal 4 * ENNReal.ofReal (r x) + ENNReal.ofReal 4 * ENNReal.ofReal (e x)) ∂gaugeHaar +
          ENNReal.ofReal c * gaugeHaar E := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ ∫⁻ x, (ENNReal.ofReal 4 * ENNReal.ofReal (r x) + ENNReal.ofReal 4 * ENNReal.ofReal (e x)) ∂gaugeHaar +
          ENNReal.ofReal c * 1 := by
          exact add_le_add (setLIntegral_le_lintegral _ _) (by gcongr)
    _ = ENNReal.ofReal 4 * ∫⁻ x, ENNReal.ofReal (r x) ∂gaugeHaar +
          ENNReal.ofReal 4 * ∫⁻ x, ENNReal.ofReal (e x) ∂gaugeHaar + ENNReal.ofReal c := by
          rw [lintegral_add_left' (hrm.ennreal_ofReal.const_mul _), lintegral_const_mul' _ _ h4,
            lintegral_const_mul' _ _ h4, mul_one]
    _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal B₁ + ENNReal.ofReal 4 * ENNReal.ofReal B₂ + ENNReal.ofReal c := by
          gcongr
    _ = ENNReal.ofReal (4 * B₁ + 4 * B₂ + c) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) hc]

/-- The partial sums of `Σ 1/p` are not bounded. -/
theorem not_bounded_sum_primes_inv (R : ℝ) :
    ¬ ∀ N : ℕ, ∑ p ∈ N.primesBelow, (1 : ℝ) / p ≤ R := by
  intro h
  refine not_summable_one_div_on_primes (summable_of_sum_range_le (c := R) (fun n => ?_) fun n => ?_)
  · exact Set.indicator_nonneg (fun m _ => by positivity) n
  · refine le_trans (le_of_eq ?_) (h n)
    unfold Nat.primesBelow
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : m.Prime
    · simp [hm]
    · simp [hm]

/-- **Zygmund's theorem on the torus.** Let `Re s_j → ½` from the right. The sums `Σ_p p^{−s_j} x_p`, perturbed by functions bounded in `L²` uniformly in `j`, stay bounded only on a null set. -/
theorem measure_bounded_prime_sums_eq_zero {s : ℕ → ℂ} (hs : ∀ j, 1 / 2 < (s j).re)
    (hlim : Tendsto (fun j => (s j).re) atTop (𝓝 (1 / 2)))
    {g e : ℕ → GaugeTorus → ℂ}
    (hg : ∀ j, ∀ᵐ x ∂gaugeHaar, Tendsto (fun N => primeSum N (s j) x) atTop (𝓝 (g j x)))
    (he : ∀ j, AEMeasurable (e j) gaugeHaar) {C : ℝ} (hC0 : 0 ≤ C)
    (heL : ∀ j, ∫⁻ x, ENNReal.ofReal (‖e j x‖ ^ 2) ∂gaugeHaar ≤ ENNReal.ofReal C) (M : ℝ) (J : ℕ) :
    gaugeHaar {x | ∀ j, J ≤ j → ‖g j x + e j x‖ ≤ M} = 0 := by
  classical
  have hgm : ∀ j, AEMeasurable (g j) gaugeHaar := fun j =>
    aemeasurable_of_tendsto_metrizable_ae atTop
      (fun N => (continuous_primeSum N (s j)).aemeasurable) (hg j)
  -- A measurable set carrying the bound.
  set v : ℕ → GaugeTorus → ℂ := fun j => ((hgm j).add (he j)).mk _ with hv
  have hvm : ∀ j, Measurable (v j) := fun j => ((hgm j).add (he j)).measurable_mk
  have hve : ∀ᵐ x ∂gaugeHaar, ∀ j, g j x + e j x = v j x :=
    ae_all_iff.mpr fun j => ((hgm j).add (he j)).ae_eq_mk
  set E : Set GaugeTorus := ⋂ j, ⋂ (_ : J ≤ j), {x | ‖v j x‖ ≤ M} with hE
  have hEm : MeasurableSet E := MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_le (hvm j).norm measurable_const
  have hsub : {x | ∀ j, J ≤ j → ‖g j x + e j x‖ ≤ M} ≤ᵐ[gaugeHaar] E := by
    filter_upwards [hve] with x hx hZ
    show x ∈ E
    refine Set.mem_iInter.mpr fun j => Set.mem_iInter.mpr fun hj => ?_
    show ‖v j x‖ ≤ M
    rw [← hx j]
    exact hZ j hj
  refine le_antisymm ((measure_mono_ae hsub).trans (le_of_eq ?_)) zero_le
  by_contra hne
  set m : ℝ := (gaugeHaar E).toReal with hm
  have hm0 : 0 < m := ENNReal.toReal_pos hne (measure_ne_top _ _)
  obtain ⟨P, hP⟩ := exists_tail_corr_small E (ε := (m / 2) ^ 2) (by positivity)
  set S : ℕ → ℕ → ℝ := fun j N => ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-(2 * (s j).re)) with hS
  set T : ℕ → ℝ := fun j => ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * (s j).re)) with hT
  set K : ℝ := (P.primesBelow.card : ℝ) with hK
  have hsumm : ∀ j, Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * (s j).re)) := fun j =>
    Nat.Primes.summable_rpow.mpr (by linarith [hs j])
  have hST : ∀ j N, S j N ≤ T j := fun j N =>
    sum_primesBelow_le_tsum (g := fun p : ℕ => (p : ℝ) ^ (-(2 * (s j).re)))
      (fun p => by positivity) (hsumm j) N
  have hSmono : ∀ j, Monotone (S j) := fun j a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (primesBelow_subset hab) fun p _ _ => by positivity
  have hSlim : ∀ j, Tendsto (S j) atTop (𝓝 (T j)) := fun j =>
    tendsto_sum_primesBelow (g := fun p : ℕ => (p : ℝ) ^ (-(2 * (s j).re))) (hsumm j)
  -- The main inequality, for one exponent.
  have key : ∀ j, J ≤ j → ∀ N, P ≤ N →
      (m / 2) * (S j N - S j P) ≤ 4 * (T j - S j N) + 4 * C + (4 * M ^ 2 + 4 * K ^ 2) := by
    intro j hj N hPN
    set Ps : Finset ℕ := N.primesBelow \ P.primesBelow with hPs
    have hPs' : ∀ p ∈ Ps, p.Prime ∧ P ≤ p := by
      intro p hp
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hp
      have h3 := Nat.mem_primesBelow.mp h1
      refine ⟨h3.2, ?_⟩
      by_contra h4
      exact h2 (Nat.mem_primesBelow.mpr ⟨by omega, h3.2⟩)
    have h1 := le_setIntegral_normSq (E := E) Ps (powCoeff (s j)) (τ := m / 2) (by positivity)
      (hP Ps hPs')
    have hsumPs : ∑ p ∈ Ps, ‖powCoeff (s j) p‖ ^ 2 = S j N - S j P := by
      rw [Finset.sum_congr rfl fun p hp => norm_powCoeff_sq (hPs' p hp).1.pos (s j)]
      exact Finset.sum_sdiff_eq_sub (primesBelow_subset hPN)
    rw [hsumPs] at h1
    have hAc : Continuous fun x : GaugeTorus => ‖∑ p ∈ Ps, powCoeff (s j) p * twist x p‖ ^ 2 := by
      have : Continuous fun x : GaugeTorus => twistSum Ps (powCoeff (s j)) x := continuous_twistSum _ _
      exact this.norm.pow 2
    have h2 : ENNReal.ofReal (∫ x in E, ‖∑ p ∈ Ps, powCoeff (s j) p * twist x p‖ ^ 2 ∂gaugeHaar) =
        ∫⁻ x in E, ENNReal.ofReal (‖∑ p ∈ Ps, powCoeff (s j) p * twist x p‖ ^ 2) ∂gaugeHaar :=
      ofReal_integral_eq_lintegral_ofReal (integrable_of_continuous_torus hAc).integrableOn
        (Eventually.of_forall fun x => by positivity)
    have hrm : AEMeasurable (fun x => ‖g j x - primeSum N (s j) x‖ ^ 2) gaugeHaar :=
      (((hgm j).sub (continuous_primeSum N (s j)).aemeasurable).norm).pow_const 2
    have h3 := setLIntegral_ofReal_le (E := E)
      (f := fun x => ‖∑ p ∈ Ps, powCoeff (s j) p * twist x p‖ ^ 2)
      (r := fun x => ‖g j x - primeSum N (s j) x‖ ^ 2) (e := fun x => ‖e j x‖ ^ 2)
      (c := 4 * M ^ 2 + 4 * K ^ 2) (B₁ := T j - S j N) (B₂ := C) (by positivity)
      (by linarith [hST j N]) hC0 (fun x => by positivity) (fun x => by positivity) hrm ?_
      (lintegral_sub_primeSum_le (hST j) (hg j) N) (heL j)
    · rw [← h2] at h3
      have h4 := (ENNReal.ofReal_le_ofReal_iff (by
        have := hST j N
        nlinarith [sq_nonneg M, sq_nonneg K])).mp h3
      have h5 : (gaugeHaar E).toReal - m / 2 = m / 2 := by
        rw [← hm]
        ring
      rw [h5] at h1
      linarith
    · filter_upwards [ae_restrict_mem hEm, ae_restrict_of_ae hve] with x hxE hx
      have hb : ‖v j x‖ ≤ M := Set.mem_iInter.mp (Set.mem_iInter.mp hxE j) hj
      have hb2 : ‖v j x‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      have hq2 : ‖primeSum P (s j) x‖ ^ 2 ≤ K ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_primeSum_le P (by linarith [hs j]) x) 2
      have hsplit : ∑ p ∈ Ps, powCoeff (s j) p * twist x p =
          v j x - e j x - primeSum P (s j) x - (g j x - primeSum N (s j) x) := by
        have h6 : primeSum N (s j) x = (∑ p ∈ Ps, powCoeff (s j) p * twist x p) + primeSum P (s j) x := by
          unfold primeSum twistSum
          exact (Finset.sum_sdiff (primesBelow_subset hPN)).symm
        rw [← hx j, h6]
        ring
      rw [hsplit]
      have h7 := norm_sub_sub_sub_sq_le (v j x) (e j x) (primeSum P (s j) x) (g j x - primeSum N (s j) x)
      nlinarith
  -- Let the exponent go to `½`.
  have hD : ∀ j, J ≤ j → ∀ N, S j N - S j P ≤ (2 / m) * (4 + 4 * C + (4 * M ^ 2 + 4 * K ^ 2)) := by
    intro j hj N
    have hev : ∀ᶠ N' in atTop, T j - S j N' < 1 := by
      have h1 : Tendsto (fun N' => T j - S j N') atTop (𝓝 (T j - T j)) := (hSlim j).const_sub _
      rw [sub_self] at h1
      exact h1.eventually (gt_mem_nhds one_pos)
    obtain ⟨N', hN1, hN2⟩ := (hev.and (eventually_ge_atTop (max N P))).exists
    have h2 := key j hj N' (le_trans (le_max_right _ _) hN2)
    have h3 := hSmono j (le_trans (le_max_left _ _) hN2)
    have h4 : (m / 2) * (S j N - S j P) ≤ 4 + 4 * C + (4 * M ^ 2 + 4 * K ^ 2) := by
      have h5 : (m / 2) * (S j N - S j P) ≤ (m / 2) * (S j N' - S j P) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
    nlinarith
  have hLim : ∀ N : ℕ, Tendsto (fun j => S j N) atTop (𝓝 (∑ p ∈ N.primesBelow, (1 : ℝ) / p)) := by
    intro N
    refine tendsto_finsetSum _ fun p hp => ?_
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.ne_zero
    have h1 : Tendsto (fun j => (p : ℝ) ^ (-(2 * (s j).re))) atTop (𝓝 ((p : ℝ) ^ (-(2 * (1 / 2 : ℝ))))) :=
      (Real.continuousAt_const_rpow hp0).tendsto.comp (hlim.const_mul 2).neg
    rwa [show -(2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one, ← one_div] at h1
  refine not_bounded_sum_primes_inv ((2 / m) * (4 + 4 * C + (4 * M ^ 2 + 4 * K ^ 2)) +
    ∑ p ∈ P.primesBelow, (1 : ℝ) / p) fun N => ?_
  have h1 := le_of_tendsto ((hLim N).sub (hLim P))
    ((eventually_ge_atTop J).mono fun j hj => hD j hj N)
  linarith

end

end GaloisForLFunctions.PrimeTorusTheory
