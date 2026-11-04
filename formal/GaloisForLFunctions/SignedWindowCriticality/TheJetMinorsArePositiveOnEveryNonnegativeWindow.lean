import GaloisForLFunctions.SignedWindowCriticality.WindowEigenfunctionsAreSingularAtTheEdge
import Mathlib.Analysis.Matrix.PosDef

/-!
# The jet minors are positive on every nonnegative window

DRAFT
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis DimensionZeroGeometryOfSpecZ
open GrowingWindowsOfSpecZ

variable {φ : ℝ → ℝ}

/-! ### The jets of a bump are linearly independent -/

theorem contDiff_sum_smul_iteratedDeriv (hφ : ContDiff ℝ ∞ φ) {n : ℕ} (c : Fin n → ℝ) :
    ContDiff ℝ ∞ (∑ i : Fin n, c i • iteratedDeriv i φ) := by
  have e : (∑ i : Fin n, c i • iteratedDeriv i φ) = fun x => ∑ i : Fin n, c i * iteratedDeriv i φ x := by
    funext x; simp [Finset.sum_apply]
  rw [e]
  exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_iteratedDeriv_of_smooth hφ i)

theorem deriv_sum_smul_iteratedDeriv (hφ : ContDiff ℝ ∞ φ) {n : ℕ} (c : Fin n → ℝ) :
    deriv (∑ i : Fin n, c i • iteratedDeriv i φ) = ∑ i : Fin n, c i • iteratedDeriv (i + 1) φ := by
  funext u
  have hd : ∀ i : Fin n, DifferentiableAt ℝ (c i • iteratedDeriv i φ) u := fun i =>
    ((contDiff_iteratedDeriv_of_smooth hφ i).differentiable (by simp) u).const_smul (c i)
  rw [deriv_sum fun i _ => hd i, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, iteratedDeriv_succ, smul_eq_mul]
  exact deriv_const_mul _ ((contDiff_iteratedDeriv_of_smooth hφ i).differentiable (by simp) u)

/-- **A linear recurrence of the jets forces geometric growth**: if
`φ^{(m+1)} = Σ_{i≤m} a_i φ^{(i)}`, every jet is `Σ_i c_i φ^{(i)}` with `|c_i| ≤ (1 + Σ|a|)^k`. -/
theorem exists_jet_coeffs (hφ : ContDiff ℝ ∞ φ) {m : ℕ} (a : Fin (m + 1) → ℝ)
    (hrec : iteratedDeriv (m + 1) φ = ∑ i : Fin (m + 1), a i • iteratedDeriv i φ) :
    ∀ k : ℕ, ∃ c : Fin (m + 1) → ℝ, (∀ i, |c i| ≤ (1 + ∑ j, |a j|) ^ k) ∧
      iteratedDeriv k φ = ∑ i : Fin (m + 1), c i • iteratedDeriv i φ := by
  set B := 1 + ∑ j, |a j|
  have hB : 1 ≤ B := by
    have : 0 ≤ ∑ j, |a j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    simp only [B]; linarith
  intro k
  induction k with
  | zero =>
    refine ⟨Pi.single 0 1, fun i => ?_, ?_⟩
    · by_cases hi : i = 0
      · subst hi; simp
      · simp [Pi.single_apply, hi]
    · rw [Finset.sum_eq_single 0 (fun i _ hi => by simp [hi]) (by simp)]
      simp
  | succ k ih =>
    obtain ⟨c, hc, hk⟩ := ih
    set c' : Fin (m + 1) → ℝ := fun j =>
      (Fin.cases 0 (fun i : Fin m => c (Fin.castSucc i)) j : ℝ) + c (Fin.last m) * a j
    refine ⟨c', fun j => ?_, ?_⟩
    · have h1 : |(Fin.cases 0 (fun i : Fin m => c (Fin.castSucc i)) j : ℝ)| ≤ B ^ k := by
        refine Fin.cases ?_ (fun i => ?_) j
        · simp only [Fin.cases_zero, abs_zero]; positivity
        · simp only [Fin.cases_succ]; exact hc _
      have h2 : |a j| ≤ ∑ j, |a j| :=
        Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
      calc |c' j| ≤ |(Fin.cases 0 (fun i : Fin m => c (Fin.castSucc i)) j : ℝ)| +
            |c (Fin.last m)| * |a j| := by
            simp only [c']; rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ B ^ k + B ^ k * (∑ j, |a j|) :=
            add_le_add h1 (mul_le_mul (hc _) h2 (abs_nonneg _) (by positivity))
        _ = B ^ (k + 1) := by simp only [B]; ring
    · rw [iteratedDeriv_succ, hk, deriv_sum_smul_iteratedDeriv hφ, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [hrec]
      have hR : ∑ j : Fin (m + 1), c' j • iteratedDeriv j φ =
          ∑ i : Fin m, c (Fin.castSucc i) • iteratedDeriv (i + 1) φ +
            c (Fin.last m) • ∑ j : Fin (m + 1), a j • iteratedDeriv j φ := by
        simp only [c', add_smul, Finset.sum_add_distrib, mul_smul]
        rw [← Finset.smul_sum, Fin.sum_univ_succ]
        simp only [Fin.cases_zero, Fin.cases_succ, zero_smul, zero_add, Fin.val_succ]
      rw [hR]

/-- **A bump satisfying a linear differential equation with constant coefficients vanishes.** -/
theorem eq_zero_of_iteratedDeriv_eq_sum (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {m : ℕ} (a : Fin (m + 1) → ℝ)
    (hrec : iteratedDeriv (m + 1) φ = ∑ i : Fin (m + 1), a i • iteratedDeriv i φ) : φ = 0 := by
  set B := 1 + ∑ j, |a j|
  have hB : 0 ≤ B := by
    have : 0 ≤ ∑ j, |a j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    simp only [B]; linarith
  set S := ∑ i : Fin (m + 1), jetNormSq φ i
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => jetNormSq_nonneg φ i
  refine eq_zero_of_sq_iteratedDeriv_le hφ hφc (C := ((m : ℝ) + 1) * S) (B := B ^ 2) (by positivity)
    (by positivity) fun k => ?_
  obtain ⟨c, hc, hk⟩ := exists_jet_coeffs hφ a hrec k
  have hint : ∀ i : Fin (m + 1), Integrable fun u => iteratedDeriv i φ u ^ 2 := fun i =>
    integrable_sq_of_continuous (contDiff_iteratedDeriv_of_smooth hφ i).continuous
      (iteratedDeriv_mem_realTests hφ hφc i).2
  have hpt : ∀ u, iteratedDeriv k φ u ^ 2 ≤
      ((m : ℝ) + 1) * (B ^ 2) ^ k * ∑ i : Fin (m + 1), iteratedDeriv i φ u ^ 2 := by
    intro u
    rw [hk, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i : Fin (m + 1) => c i * iteratedDeriv i φ u)
    simp only [Finset.card_univ, Fintype.card_fin] at hcs
    refine hcs.trans ?_
    push_cast
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_pow, ← pow_mul, show B ^ (2 * k) = (B ^ k) ^ 2 by rw [← pow_mul, mul_comm]]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs (c i)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hc i) 2
  calc ∫ u, iteratedDeriv k φ u ^ 2 ≤
        ∫ u, ((m : ℝ) + 1) * (B ^ 2) ^ k * ∑ i : Fin (m + 1), iteratedDeriv i φ u ^ 2 :=
        integral_mono (integrable_sq_of_continuous
          (contDiff_iteratedDeriv_of_smooth hφ k).continuous
          (iteratedDeriv_mem_realTests hφ hφc k).2)
          ((integrable_finsetSum _ fun i _ => hint i).const_mul _) hpt
    _ = ((m : ℝ) + 1) * S * (B ^ 2) ^ k := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ => hint i]
        simp only [S, jetNormSq]
        ring

/-- **The jets of a nonzero bump are linearly independent.** -/
theorem eq_zero_of_sum_smul_iteratedDeriv (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : φ ≠ 0) :
    ∀ (n : ℕ) (x : Fin n → ℝ), ∑ i : Fin n, x i • iteratedDeriv i φ = 0 → x = 0 := by
  intro n
  induction n with
  | zero => intro x _; exact Subsingleton.elim _ _
  | succ n ih =>
    intro x hx
    rw [Fin.sum_univ_castSucc] at hx
    simp only [Fin.val_castSucc, Fin.val_last] at hx
    have hlast : x (Fin.last n) = 0 := by
      by_contra hl
      apply hφ0
      cases n with
      | zero =>
        simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at hx
        have := congrFun hx
        funext u
        have hu := this u
        simp only [Pi.smul_apply, iteratedDeriv_zero, smul_eq_mul, Pi.zero_apply,
          mul_eq_zero] at hu
        rcases hu with h | h
        · exact absurd h hl
        · exact h
      | succ m =>
        refine eq_zero_of_iteratedDeriv_eq_sum hφ hφc (m := m)
          (fun i => -(x (Fin.castSucc i)) / x (Fin.last (m + 1))) ?_
        have h := eq_neg_of_add_eq_zero_right hx
        rw [← smul_right_inj hl, h, ← Finset.sum_neg_distrib, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, ← neg_smul]
        congr 1
        field_simp
    rw [hlast, zero_smul, add_zero] at hx
    have hrest := ih (fun i => x (Fin.castSucc i)) hx
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · exact hlast
    · exact congrFun hrest i

/-! ### Positive definite windows have positive definite jet Gram matrices -/

theorem weilPair_sum_smul_sum_smul {n : ℕ} {f : Fin n → ℝ → ℝ} (hf : ∀ i, f i ∈ realTests)
    (x : Fin n → ℝ) :
    weilPair (∑ i, x i • f i) (∑ j, x j • f j) = ∑ i, x i * ∑ j, weilPair (f i) (f j) * x j := by
  have hfs : ∀ i, x i • f i ∈ realTests := fun i => realTests.smul_mem _ (hf i)
  have hsum : (∑ j, x j • f j) ∈ realTests := Submodule.sum_mem _ fun j _ => hfs j
  rw [weilPair_sum_left _ hfs hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [weilPair_smul_left, weilPair_sum_right _ hfs (hf i)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weilPair_smul_right]; ring

/-- **The jet Gram matrix is positive definite** on every window on which Weil's form is positive
definite on smooth tests. -/
theorem jetGram_posDef {a : ℝ}
    (hpd : ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → SupportedIn a F → F ≠ 0 → 0 < weilQuad F)
    (hφ : ContDiff ℝ ∞ φ) (hφa : SupportedIn a φ) (hφ0 : φ ≠ 0) (n : ℕ) :
    (jetGram φ n).PosDef := by
  have hφc := hasCompactSupport_of_supportedIn' hφa
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp [jetGram, Matrix.conjTranspose_apply, weilPair_comm]
  · set F := ∑ i : Fin n, x i • iteratedDeriv i φ
    have hF : ContDiff ℝ ∞ F := contDiff_sum_smul_iteratedDeriv hφ x
    have hFa : SupportedIn a F := fun u hu => by
      simp only [F, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_eq_zero fun i _ => by rw [iteratedDeriv_supportedIn hφa i u hu, mul_zero]
    have hF0 : F ≠ 0 := fun h => hx (eq_zero_of_sum_smul_iteratedDeriv hφ hφc hφ0 n x h)
    have hpos := hpd F hF hFa hF0
    have hexp : weilQuad F = ∑ i, x i * ∑ j, jetGram φ n i j * x j :=
      weilPair_sum_smul_sum_smul (fun i => iteratedDeriv_mem_realTests hφ hφc i) x
    simp only [star_trivial, dotProduct, Matrix.mulVec]
    rw [hexp] at hpos
    simpa [dotProduct] using hpos

/-- **The jet minors are positive**: `det J_n(φ) > 0` for every `n` and every nonzero smooth bump on
a window on which Weil's form is positive definite on smooth tests. -/
theorem det_jetGram_pos {a : ℝ}
    (hpd : ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → SupportedIn a F → F ≠ 0 → 0 < weilQuad F)
    (hφ : ContDiff ℝ ∞ φ) (hφa : SupportedIn a φ) (hφ0 : φ ≠ 0) (n : ℕ) :
    0 < (jetGram φ n).det :=
  (jetGram_posDef hpd hφ hφa hφ0 n).det_pos

/-- **On a nonnegative window the continuum canonical system of every nonzero smooth bump is
nondegenerate**: all jet minors are positive, and the lattice margins satisfy
`h^{−2n}E_n(φ, h) → det J_{n+1}/det J_n > 0`. -/
theorem tendsto_levinsonErr_div_pow_of_window_nonneg {a : ℝ}
    (hnn : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → 0 ≤ weilQuad G)
    (hφ : ContDiff ℝ ∞ φ) (hφa : SupportedIn a φ) (hφ0 : φ ≠ 0) (n : ℕ) :
    0 < (jetGram φ (n + 1)).det / (jetGram φ n).det ∧
      Tendsto (fun h => levinsonErr (weilSeq φ h) n / h ^ (2 * n)) (𝓝[>] 0)
        (𝓝 ((jetGram φ (n + 1)).det / (jetGram φ n).det)) := by
  have hpd : ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → SupportedIn a F → F ≠ 0 → 0 < weilQuad F :=
    fun F hF hFa hF0 => weilQuad_pos_of_window_nonneg hnn hF hFa hF0
  exact ⟨div_pos (det_jetGram_pos hpd hφ hφa hφ0 _) (det_jetGram_pos hpd hφ hφa hφ0 _),
    tendsto_levinsonErr_div_pow hφ (hasCompactSupport_of_supportedIn' hφa) n
      fun k _ => (det_jetGram_pos hpd hφ hφa hφ0 _).ne'⟩

/-- Weil's form is positive definite on the smooth tests of the base window `2a ≤ 181/250`. -/
theorem weilQuad_pos_of_base {a : ℝ} (ha : 2 * a ≤ 181 / 250) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFa : SupportedIn a F) (hF0 : F ≠ 0) : 0 < weilQuad F :=
  GrowingWindowsOfSpecZ.weilQuad_pos_of_short (smooth_mem_realTests hF hFa) hF0 ha
    fun u hu => hFa u (lt_abs_of_notMem_Icc' (by
      intro h; apply hu; constructor <;> linarith [h.1, h.2]))

/-- **Unconditionally on the base window**: for every nonzero smooth bump supported in `[−a, a]`,
`2a ≤ 181/250`, the jet minors are positive and `h^{−2n}E_n(φ, h) → det J_{n+1}/det J_n > 0`. -/
theorem tendsto_levinsonErr_div_pow_of_base {a : ℝ} (ha : 2 * a ≤ 181 / 250)
    (hφ : ContDiff ℝ ∞ φ) (hφa : SupportedIn a φ) (hφ0 : φ ≠ 0) (n : ℕ) :
    0 < (jetGram φ (n + 1)).det / (jetGram φ n).det ∧
      Tendsto (fun h => levinsonErr (weilSeq φ h) n / h ^ (2 * n)) (𝓝[>] 0)
        (𝓝 ((jetGram φ (n + 1)).det / (jetGram φ n).det)) := by
  have hpd := fun F (hF : ContDiff ℝ ∞ F) (hFa : SupportedIn a F) (hF0 : F ≠ 0) =>
    weilQuad_pos_of_base ha hF hFa hF0
  exact ⟨div_pos (det_jetGram_pos hpd hφ hφa hφ0 _) (det_jetGram_pos hpd hφ hφa hφ0 _),
    tendsto_levinsonErr_div_pow hφ (hasCompactSupport_of_supportedIn' hφa) n
      fun k _ => (det_jetGram_pos hpd hφ hφa hφ0 _).ne'⟩

/-! ### Strict log-convexity of the jet energies -/

/-- A quadratic `At² + 2Ct + B > 0` for every `t`, `A > 0`, has `C² < AB`. -/
theorem sq_lt_mul_of_forall_pos {A B C : ℝ} (hA : 0 < A) (h : ∀ t : ℝ, 0 < A * t ^ 2 + 2 * C * t + B) :
    C ^ 2 < A * B := by
  have := h (-C / A)
  have e : A * (-C / A) ^ 2 + 2 * C * (-C / A) + B = B - C ^ 2 / A := by field_simp; ring
  rw [e, sub_pos, div_lt_iff₀ hA] at this
  linarith

/-- **The jet energies are strictly log-convex** on a positive definite window:
`W(φ^{(m+1)})² < W(φ^{(m)}) W(φ^{(m+2)})`. -/
theorem weilQuad_iteratedDeriv_sq_lt {a : ℝ}
    (hpd : ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → SupportedIn a F → F ≠ 0 → 0 < weilQuad F)
    (hφ : ContDiff ℝ ∞ φ) (hφa : SupportedIn a φ) (hφ0 : φ ≠ 0) (m : ℕ) :
    weilQuad (iteratedDeriv (m + 1) φ) ^ 2 <
      weilQuad (iteratedDeriv m φ) * weilQuad (iteratedDeriv (m + 2) φ) := by
  have hφc := hasCompactSupport_of_supportedIn' hφa
  set p := iteratedDeriv m φ
  set q := iteratedDeriv (m + 2) φ
  have hp := iteratedDeriv_mem_realTests hφ hφc m
  have hq := iteratedDeriv_mem_realTests hφ hφc (m + 2)
  -- `W(φ^{(m)}, φ^{(m+2)}) = −W(φ^{(m+1)})`
  have hskew : weilPair p q = -weilQuad (iteratedDeriv (m + 1) φ) := by
    have := weilPair_iteratedDeriv_succ_right hφ hφc m (m + 1)
    rw [show m + 1 + 1 = m + 2 by ring] at this
    exact this
  have hA : 0 < weilQuad p := by
    refine hpd p (contDiff_iteratedDeriv_of_smooth hφ m) (iteratedDeriv_supportedIn hφa m) ?_
    intro h0
    have := eq_zero_of_sum_smul_iteratedDeriv hφ hφc hφ0 (m + 1) (Pi.single (Fin.last m) 1) (by
      rw [Finset.sum_eq_single (Fin.last m) (fun i _ hi => by simp [hi])
        (by simp)]
      simpa using h0)
    simpa using congrFun this (Fin.last m)
  have hquad : ∀ t : ℝ, 0 < weilQuad p * t ^ 2 + 2 * weilPair p q * t + weilQuad q := by
    intro t
    set F := t • p + q
    have hF0 : F ≠ 0 := by
      intro h
      apply hφ0
      refine eq_zero_of_iteratedDeriv_eq_sum hφ hφc (m := m + 1)
        (Pi.single ⟨m, by omega⟩ (-t)) ?_
      rw [Finset.sum_eq_single ⟨m, by omega⟩ (fun i _ hi => by simp [hi])
        (by simp)]
      have hq' : q = -(t • p) := eq_neg_of_add_eq_zero_right h
      simp only [Pi.single_eq_same]
      rw [show m + 1 + 1 = m + 2 by ring, show iteratedDeriv (m + 2) φ = q from rfl, hq',
        neg_smul]
    have hpos := hpd F ((contDiff_iteratedDeriv_of_smooth hφ m).const_smul t |>.add
      (contDiff_iteratedDeriv_of_smooth hφ (m + 2))) (fun u hu => by
        simp only [F, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [show p u = 0 from iteratedDeriv_supportedIn hφa m u hu,
          show q u = 0 from iteratedDeriv_supportedIn hφa (m + 2) u hu]
        ring)
      hF0
    have htp : t • p ∈ realTests := realTests.smul_mem t hp
    rw [show F = t • p + q from rfl, weilQuad_add htp hq] at hpos
    have e1 : weilQuad (t • p) = t ^ 2 * weilQuad p := by
      show weilPair (t • p) (t • p) = _
      rw [weilPair_smul_left, weilPair_smul_right, show weilQuad p = weilPair p p from rfl]; ring
    rw [e1, weilPair_smul_left] at hpos
    linarith
  have := sq_lt_mul_of_forall_pos hA hquad
  rw [hskew, neg_sq] at this
  exact this

end GaloisForLFunctions.SignedWindowCriticality

end
