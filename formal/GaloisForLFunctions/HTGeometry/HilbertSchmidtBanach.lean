import GaloisForLFunctions.HTGeometry.HilbertSchmidtNormComparison

/-!
# Banach fixed point in the Hilbert–Schmidt metric

A map of the C\*-algebra that contracts in the Hilbert–Schmidt norm on the Hilbert–Schmidt ball
around a point has a fixed point in that ball.  The Hilbert–Schmidt operators are not carried as a
bundled space here: completeness is supplied by `exists_hsNorm_limit`, so the whole argument stays
inside `E →L[ℂ] E` and no dependent packaging is needed.
-/

open scoped BigOperators
open Filter Topology ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Self-adjointness passes to Hilbert–Schmidt limits. -/
lemma isSelfAdjoint_of_hs_limit {Yn : ℕ → (E →L[ℂ] E)} {Z : E →L[ℂ] E}
    (hsa : ∀ n, IsSelfAdjoint (Yn n)) (hHS : ∀ n, IsHilbertSchmidt (Yn n - Z))
    (hlim : Tendsto (fun n => hsNorm (Yn n - Z)) atTop (nhds 0)) : IsSelfAdjoint Z := by
  have hnorm : Tendsto (fun n => ‖Yn n - Z‖) atTop (nhds 0) := by
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => norm_le_hsNorm (hHS n)) hlim
  have hconv : Tendsto Yn atTop (nhds Z) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact hnorm
  have hstar : Tendsto (fun n => star (Yn n)) atTop (nhds (star Z)) :=
    (continuous_star.tendsto Z).comp hconv
  have heq : (fun n => star (Yn n)) = Yn := funext fun n => (hsa n).star_eq
  rw [heq] at hstar
  exact tendsto_nhds_unique hstar hconv

/-- **Banach fixed point in the Hilbert–Schmidt metric.** -/
theorem exists_fixedPoint_hs {G : (E →L[ℂ] E) → (E →L[ℂ] E)} {X₀ : E →L[ℂ] E} {r θ : ℝ}
    {P : (E →L[ℂ] E) → Prop} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hP0 : P X₀)
    (hPG : ∀ X : E →L[ℂ] E, P X → IsHilbertSchmidt (X - X₀) → hsNorm (X - X₀) ≤ r → P (G X))
    (hPclosed : ∀ (Y : ℕ → (E →L[ℂ] E)) (Z : E →L[ℂ] E), (∀ n, P (Y n)) →
      (∀ n, IsHilbertSchmidt (Y n - Z)) → Tendsto (fun n => hsNorm (Y n - Z)) atTop (nhds 0) →
      P Z)
    (hmaps : ∀ X : E →L[ℂ] E, P X → IsHilbertSchmidt (X - X₀) → hsNorm (X - X₀) ≤ r →
      IsHilbertSchmidt (G X - X₀))
    (hcontr : ∀ X Y : E →L[ℂ] E, P X → IsHilbertSchmidt (X - X₀) → hsNorm (X - X₀) ≤ r →
      P Y → IsHilbertSchmidt (Y - X₀) → hsNorm (Y - X₀) ≤ r →
      hsNorm (G X - G Y) ≤ θ * hsNorm (X - Y))
    (hstart : hsNorm (G X₀ - X₀) ≤ (1 - θ) * r) :
    ∃ X : E →L[ℂ] E, P X ∧ IsHilbertSchmidt (X - X₀) ∧ hsNorm (X - X₀) ≤ r ∧ G X = X := by
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  obtain ⟨d, hddef, hdnn⟩ : ∃ d : ℝ, d = hsNorm (G X₀ - X₀) ∧ 0 ≤ d :=
    ⟨_, rfl, hsNorm_nonneg _⟩
  have hrnn : (0 : ℝ) ≤ r := by nlinarith [hstart, hdnn, h1θ]
  obtain ⟨Xn, hX0, hXstep⟩ : ∃ Xn : ℕ → (E →L[ℂ] E), Xn 0 = X₀ ∧ ∀ n, Xn (n + 1) = G (Xn n) :=
    ⟨fun n => G^[n] X₀, rfl, fun n => Function.iterate_succ_apply' G n X₀⟩
  -- the invariants
  have hinv : ∀ n, P (Xn n) ∧ IsHilbertSchmidt (Xn n - X₀)
      ∧ hsNorm (Xn n - X₀) ≤ (1 - θ ^ n) / (1 - θ) * d
      ∧ hsNorm (Xn (n + 1) - Xn n) ≤ θ ^ n * d := by
    intro n
    induction n with
    | zero =>
      refine ⟨by rw [hX0]; exact hP0,
        by rw [hX0, sub_self]; exact isHilbertSchmidt_zero, ?_, ?_⟩
      · rw [hX0, sub_self, hsNorm_zero]
        simp
      · rw [hXstep, hX0, pow_zero, one_mul, hddef]
    | succ n ih =>
      obtain ⟨ihP, ihHS, ihb, ihs⟩ := ih
      have hbr : hsNorm (Xn n - X₀) ≤ r := by
        have hle : (1 - θ ^ n) / (1 - θ) * d ≤ r := by
          have hp : (0 : ℝ) ≤ θ ^ n := pow_nonneg hθ0 n
          have h2 : (1 - θ ^ n) / (1 - θ) * d ≤ 1 / (1 - θ) * d := by
            refine mul_le_mul_of_nonneg_right ?_ hdnn
            rw [div_le_div_iff_of_pos_right h1θ]
            linarith
          refine h2.trans ?_
          rw [one_div, inv_mul_eq_div, div_le_iff₀ h1θ]
          rw [hddef]
          nlinarith [hstart]
        linarith [ihb, hle]
      have hnextP : P (Xn (n + 1)) := by rw [hXstep]; exact hPG (Xn n) ihP ihHS hbr
      have hnextHS : IsHilbertSchmidt (Xn (n + 1) - X₀) := by
        rw [hXstep]; exact hmaps (Xn n) ihP ihHS hbr
      have hdiffHS : IsHilbertSchmidt (Xn (n + 1) - Xn n) := by
        have h := hnextHS.sub ihHS
        rwa [show (Xn (n + 1) - X₀) - (Xn n - X₀) = Xn (n + 1) - Xn n by abel] at h
      have hsplit : Xn (n + 1) - X₀ = (Xn (n + 1) - Xn n) + (Xn n - X₀) := by abel
      have htri : hsNorm (Xn (n + 1) - X₀)
          ≤ hsNorm (Xn (n + 1) - Xn n) + hsNorm (Xn n - X₀) := by
        rw [hsplit]
        exact hsNorm_add_le hdiffHS ihHS
      have hgeo : (1 - θ ^ n) / (1 - θ) * d + θ ^ n * d
          = (1 - θ ^ (n + 1)) / (1 - θ) * d := by
        field_simp; ring
      have hb1 : hsNorm (Xn (n + 1) - X₀) ≤ (1 - θ ^ (n + 1)) / (1 - θ) * d := by
        linarith [htri, ihs, ihb, hgeo]
      refine ⟨hnextP, hnextHS, hb1, ?_⟩
      have hbr1 : hsNorm (Xn (n + 1) - X₀) ≤ r := by
        have hp : (0 : ℝ) ≤ θ ^ (n + 1) := pow_nonneg hθ0 _
        have h2 : (1 - θ ^ (n + 1)) / (1 - θ) * d ≤ 1 / (1 - θ) * d := by
          refine mul_le_mul_of_nonneg_right ?_ hdnn
          rw [div_le_div_iff_of_pos_right h1θ]
          linarith
        have h3 : 1 / (1 - θ) * d ≤ r := by
          rw [one_div, inv_mul_eq_div, div_le_iff₀ h1θ, hddef]
          nlinarith [hstart]
        linarith [hb1, h2, h3]
      have hc := hcontr (Xn (n + 1)) (Xn n) hnextP hnextHS hbr1 ihP ihHS hbr
      rw [← hXstep, ← hXstep] at hc
      calc hsNorm (Xn (n + 1 + 1) - Xn (n + 1)) ≤ θ * hsNorm (Xn (n + 1) - Xn n) := hc
        _ ≤ θ * (θ ^ n * d) := mul_le_mul_of_nonneg_left ihs hθ0
        _ = θ ^ (n + 1) * d := by ring
  -- consequences of the invariants
  have hPall : ∀ n, P (Xn n) := fun n => (hinv n).1
  have hHSall : ∀ n, IsHilbertSchmidt (Xn n - X₀) := fun n => (hinv n).2.1
  have hgeo1 : 1 / (1 - θ) * d ≤ r := by
    rw [one_div, inv_mul_eq_div, div_le_iff₀ h1θ, hddef]
    nlinarith [hstart]
  have hbndall : ∀ n, hsNorm (Xn n - X₀) ≤ r := by
    intro n
    have hp : (0 : ℝ) ≤ θ ^ n := pow_nonneg hθ0 n
    have h2 : (1 - θ ^ n) / (1 - θ) * d ≤ 1 / (1 - θ) * d := by
      refine mul_le_mul_of_nonneg_right ?_ hdnn
      rw [div_le_div_iff_of_pos_right h1θ]
      linarith
    linarith [(hinv n).2.2.1, h2, hgeo1]
  have hdiffHSall : ∀ m n : ℕ, IsHilbertSchmidt (Xn m - Xn n) := by
    intro m n
    have h := (hHSall m).sub (hHSall n)
    rwa [show (Xn m - X₀) - (Xn n - X₀) = Xn m - Xn n by abel] at h
  have hsymm : ∀ A B : E →L[ℂ] E, hsNorm (A - B) = hsNorm (B - A) := by
    intro A B
    show Real.sqrt (hsNormSq _) = Real.sqrt (hsNormSq _)
    rw [show (A - B : E →L[ℂ] E) = -(B - A) by abel, hsNormSq_neg_eq_self]
  -- the Cauchy estimate
  have hcau : ∀ n m : ℕ, n ≤ m → hsNorm (Xn m - Xn n) ≤ (θ ^ n - θ ^ m) / (1 - θ) * d := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => simp [hsNorm_zero]
    | succ m hnm ih =>
      have htri : hsNorm (Xn (m + 1) - Xn n)
          ≤ hsNorm (Xn (m + 1) - Xn m) + hsNorm (Xn m - Xn n) := by
        have hsplit : Xn (m + 1) - Xn n = (Xn (m + 1) - Xn m) + (Xn m - Xn n) := by abel
        rw [hsplit]
        exact hsNorm_add_le (hdiffHSall (m + 1) m) (hdiffHSall m n)
      have hgeo : (θ ^ n - θ ^ m) / (1 - θ) * d + θ ^ m * d
          = (θ ^ n - θ ^ (m + 1)) / (1 - θ) * d := by field_simp; ring
      linarith [htri, ih, (hinv m).2.2.2, hgeo]
  have hcauchy : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      hsNorm ((Xn m - X₀) - (Xn n - X₀)) ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1) (ε * (1 - θ) / (d + 1))
      (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [show ((Xn m - X₀) - (Xn n - X₀) : E →L[ℂ] E) = Xn m - Xn n by abel]
    have hkey : ∀ k l : ℕ, N ≤ k → k ≤ l → hsNorm (Xn l - Xn k) ≤ ε := by
      intro k l hk hkl
      have hb := hcau k l hkl
      have hpk : θ ^ k < ε * (1 - θ) / (d + 1) := by
        have h := hN k hk
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hθ0 k)] at h
        exact h
      have hpl : (0 : ℝ) ≤ θ ^ l := pow_nonneg hθ0 l
      have hstep : (θ ^ k - θ ^ l) / (1 - θ) * d ≤ θ ^ k / (1 - θ) * d := by
        refine mul_le_mul_of_nonneg_right ?_ hdnn
        rw [div_le_div_iff_of_pos_right h1θ]
        linarith
      have hfin : θ ^ k / (1 - θ) * d ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ h1θ]
        have h1 : θ ^ k * (d + 1) < ε * (1 - θ) := by
          rw [lt_div_iff₀ (by positivity : (0:ℝ) < d + 1)] at hpk
          linarith
        nlinarith [pow_nonneg hθ0 k, hdnn]
      linarith [hb, hstep, hfin]
    rcases le_total n m with h | h
    · exact hkey n m hn h
    · rw [hsymm]
      exact hkey m n hm h
  obtain ⟨K, hKHS, hKlim⟩ := exists_hsNorm_limit hHSall hcauchy
  have hKb : hsNorm K ≤ r := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hKlim ε hε
    have h := hN N le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNorm_nonneg _)] at h
    have htri : hsNorm K ≤ hsNorm (Xn N - X₀) + hsNorm ((Xn N - X₀) - K) := by
      have h1 : hsNorm ((Xn N - X₀) - ((Xn N - X₀) - K))
          ≤ hsNorm (Xn N - X₀) + hsNorm ((Xn N - X₀) - K) :=
        hsNorm_sub_le (hHSall N) ((hHSall N).sub hKHS)
      rwa [show ((Xn N - X₀) - ((Xn N - X₀) - K) : E →L[ℂ] E) = K by abel] at h1
    linarith [hbndall N, h]
  have hXHS : IsHilbertSchmidt ((X₀ + K) - X₀) := by rw [add_sub_cancel_left]; exact hKHS
  have hXb : hsNorm ((X₀ + K) - X₀) ≤ r := by rw [add_sub_cancel_left]; exact hKb
  have hXP : P (X₀ + K) := by
    refine hPclosed Xn (X₀ + K) hPall (fun n => ?_) ?_
    · have h := (hHSall n).sub hKHS
      rwa [show (Xn n - X₀) - K = Xn n - (X₀ + K) by abel] at h
    · refine hKlim.congr fun n => ?_
      congr 1
      abel
  refine ⟨X₀ + K, hXP, hXHS, hXb, ?_⟩
  have hGHS : IsHilbertSchmidt (G (X₀ + K) - X₀) := hmaps _ hXP hXHS hXb
  have hdiff : IsHilbertSchmidt (G (X₀ + K) - (X₀ + K)) := by
    have h := hGHS.sub hXHS
    rwa [show (G (X₀ + K) - X₀) - ((X₀ + K) - X₀) = G (X₀ + K) - (X₀ + K) by abel] at h
  have hzero : hsNorm (G (X₀ + K) - (X₀ + K)) = 0 := by
    refine le_antisymm ?_ (hsNorm_nonneg _)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hKlim (ε / 2) (by linarith)
    have hnN := hN N le_rfl
    have hn1 := hN (N + 1) (Nat.le_succ N)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNorm_nonneg _)] at hnN hn1
    have hc := hcontr (X₀ + K) (Xn N) hXP hXHS hXb (hPall N) (hHSall N) (hbndall N)
    have hd1 : hsNorm ((X₀ + K) - Xn N) = hsNorm ((Xn N - X₀) - K) := by
      rw [hsymm]
      congr 1
      abel
    have hGXnHS : IsHilbertSchmidt (G (Xn N) - X₀) := by
      rw [← hXstep]; exact hHSall (N + 1)
    have hHS1 : IsHilbertSchmidt (G (X₀ + K) - G (Xn N)) := by
      have h := hGHS.sub hGXnHS
      rwa [show (G (X₀ + K) - X₀) - (G (Xn N) - X₀) = G (X₀ + K) - G (Xn N) by abel] at h
    have hHS2 : IsHilbertSchmidt (Xn (N + 1) - (X₀ + K)) := by
      have h := (hHSall (N + 1)).sub hKHS
      rwa [show (Xn (N + 1) - X₀) - K = Xn (N + 1) - (X₀ + K) by abel] at h
    have hsplit : G (X₀ + K) - (X₀ + K)
        = (G (X₀ + K) - G (Xn N)) + (Xn (N + 1) - (X₀ + K)) := by
      rw [hXstep]; abel
    have htri : hsNorm (G (X₀ + K) - (X₀ + K))
        ≤ hsNorm (G (X₀ + K) - G (Xn N)) + hsNorm (Xn (N + 1) - (X₀ + K)) := by
      rw [hsplit]; exact hsNorm_add_le hHS1 hHS2
    have hd2 : hsNorm (Xn (N + 1) - (X₀ + K)) = hsNorm ((Xn (N + 1) - X₀) - K) := by
      congr 1; abel
    rw [hd1] at hc
    rw [hd2] at htri
    nlinarith [htri, hc, hnN, hn1, hθ0, hθ1, hsNorm_nonneg ((Xn N - X₀) - K)]
  exact sub_eq_zero.mp ((hsNorm_eq_zero_iff hdiff).mp hzero)

end

end GaloisForLFunctions.HTGeometry
