import GaloisForLFunctions.CollectiveDiophantineGeometry.CollectiveAuxiliaryConstruction

/-!
# Analytic extrapolation in the free prime directions

The projected auxiliary differentiates in the free directions, while its
true companion retains the full prime-frequency box. The frequency error
is controlled by the sum of the absolute pivot-normalized linear forms.
-/

noncomputable section
namespace GaloisForLFunctions.CollectiveDiophantineGeometry
open Finset Complex Matrix Metric
open RHTower.Matveev

variable {r m d : ℕ} (p : Fin (m + 1) → ℕ)
  (A : Matrix (Fin r) (Fin (m + 1)) ℤ) (s : Fin r → Fin (m + 1))
  (e : Fin d → Fin (m + 1))

/-- Frequency restricted to the free projected coordinates. -/
def collectiveFreq (l : Fin (m + 1) → ℕ) : ℝ :=
  ∑ j, (collectiveGamma A s (fun i => (l i : ℤ)) (e j) : ℝ) /
    ((A.submatrix id s).det : ℝ) * Real.log (p (e j))

/-- Analytic auxiliary whose diagonal derivatives remain in the free jet family. -/
def collectiveAux (N q : ℕ) (C : FeldmanIndex N q m → ℤ)
    (σ : ℕ) (τ : Fin d → ℕ) (z : ℂ) : ℂ :=
  ∑ kl, (C kl : ℂ) * feldmanJet N kl.1 σ z * collectiveGammaWeight A s e kl.expo τ *
    Complex.exp (z * (collectiveFreq p A s e kl.expo : ℂ))

/-- Logarithmic mass of the free prime directions. -/
def collectiveFreeLogSum : ℝ := ∑ j, Real.log (p (e j))

theorem collectiveFreeLogSum_nonneg (hp : ∀ j, 1 ≤ p j) :
    0 ≤ collectiveFreeLogSum p e :=
  sum_nonneg fun j _ => Real.log_nonneg (by exact_mod_cast hp _)

/-- Raising one exponent multiplies the weight by the corresponding coordinate. -/
theorem collectiveGammaWeight_add_single (l : Fin (m + 1) → ℕ) (τ : Fin d → ℕ) (j : Fin d) :
    collectiveGammaWeight A s e l (τ + Pi.single j 1) =
      collectiveGammaWeight A s e l τ * ((collectiveGamma A s (fun i => (l i : ℤ)) (e j) : ℂ) / ((A.submatrix id s).det : ℂ)) := by
  classical
  rw [collectiveGammaWeight, collectiveGammaWeight]
  simp only [Pi.add_apply, pow_add]
  rw [prod_mul_distrib]
  congr 1
  rw [prod_eq_single j (fun i _ hij => by rw [Pi.single_eq_of_ne hij, pow_zero])
    (fun h => absurd (mem_univ j) h)]
  simp

theorem hasDerivAt_collectiveAux {N q : ℕ} (C : FeldmanIndex N q m → ℤ) (σ : ℕ) (τ : Fin d → ℕ)
    (z : ℂ) :
    HasDerivAt (collectiveAux p A s e N q C σ τ)
      (((σ : ℂ) + 1) * collectiveAux p A s e N q C (σ + 1) τ z +
        ∑ j : Fin d, (Real.log (p (e j)) : ℂ) *
          collectiveAux p A s e N q C σ (τ + Pi.single j 1) z) z := by
  unfold collectiveAux
  have hterm : ∀ kl : FeldmanIndex N q m, HasDerivAt
      (fun w => (C kl : ℂ) * feldmanJet N kl.1 σ w * collectiveGammaWeight A s e kl.expo τ *
        Complex.exp (w * (collectiveFreq p A s e kl.expo : ℂ)))
      ((C kl : ℂ) * (((σ : ℂ) + 1) * feldmanJet N kl.1 (σ + 1) z) * collectiveGammaWeight A s e kl.expo τ *
          Complex.exp (z * (collectiveFreq p A s e kl.expo : ℂ)) +
        (C kl : ℂ) * feldmanJet N kl.1 σ z * collectiveGammaWeight A s e kl.expo τ *
          (Complex.exp (z * (collectiveFreq p A s e kl.expo : ℂ)) * (collectiveFreq p A s e kl.expo : ℂ))) z := by
    intro kl
    have h1 := (((hasDerivAt_feldmanJet N kl.1 σ z).const_mul (C kl : ℂ)).mul_const
      (collectiveGammaWeight A s e kl.expo τ))
    have h2 := ((hasDerivAt_id z).mul_const (collectiveFreq p A s e kl.expo : ℂ)).cexp
    simp only [id, one_mul] at h2
    exact h1.mul h2
  refine (HasDerivAt.fun_sum fun kl _ => hterm kl).congr_deriv ?_
  have hfreq : ∀ kl : FeldmanIndex N q m, (collectiveFreq p A s e kl.expo : ℂ) =
      ∑ j : Fin d, ((collectiveGamma A s (fun i => (kl.expo i : ℤ)) (e j) : ℂ) / ((A.submatrix id s).det : ℂ)) *
        (Real.log (p (e j)) : ℂ) := by
    intro kl
    simp only [collectiveFreq, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_div, Complex.ofReal_intCast]
  calc ∑ kl : FeldmanIndex N q m,
        ((C kl : ℂ) * (((σ : ℂ) + 1) * feldmanJet N kl.1 (σ + 1) z) * collectiveGammaWeight A s e kl.expo τ *
            Complex.exp (z * (collectiveFreq p A s e kl.expo : ℂ)) +
          (C kl : ℂ) * feldmanJet N kl.1 σ z * collectiveGammaWeight A s e kl.expo τ *
            (Complex.exp (z * (collectiveFreq p A s e kl.expo : ℂ)) * (collectiveFreq p A s e kl.expo : ℂ)))
      = ∑ kl : FeldmanIndex N q m,
          (((σ : ℂ) + 1) * ((C kl : ℂ) * feldmanJet N kl.1 (σ + 1) z * collectiveGammaWeight A s e kl.expo τ *
              Complex.exp (z * (collectiveFreq p A s e kl.expo : ℂ))) +
            ∑ j : Fin d, (Real.log (p (e j)) : ℂ) *
              ((C kl : ℂ) * feldmanJet N kl.1 σ z * collectiveGammaWeight A s e kl.expo (τ + Pi.single j 1) *
                Complex.exp (z * (collectiveFreq p A s e kl.expo : ℂ)))) := by
        refine sum_congr rfl fun kl _ => ?_
        simp only [collectiveGammaWeight_add_single]
        set ζ := Complex.exp (z * (collectiveFreq p A s e kl.expo : ℂ)) with he
        rw [hfreq kl, mul_sum, mul_sum]
        congr 1
        · ring
        · refine sum_congr rfl fun j _ => ?_
          ring
    _ = ((σ : ℂ) + 1) * ∑ kl : FeldmanIndex N q m, (C kl : ℂ) * feldmanJet N kl.1 (σ + 1) z *
            collectiveGammaWeight A s e kl.expo τ * Complex.exp (z * (collectiveFreq p A s e kl.expo : ℂ)) +
          ∑ j : Fin d, (Real.log (p (e j)) : ℂ) *
            ∑ kl : FeldmanIndex N q m, (C kl : ℂ) * feldmanJet N kl.1 σ z *
              collectiveGammaWeight A s e kl.expo (τ + Pi.single j 1) *
                Complex.exp (z * (collectiveFreq p A s e kl.expo : ℂ)) := by
        rw [sum_add_distrib, mul_sum]
        congr 1
        rw [sum_comm]
        refine sum_congr rfl fun j _ => ?_
        rw [mul_sum]

theorem differentiable_collectiveAux {N q : ℕ} (C : FeldmanIndex N q m → ℤ) (σ : ℕ)
    (τ : Fin d → ℕ) : Differentiable ℂ (collectiveAux p A s e N q C σ τ) :=
  fun z => (hasDerivAt_collectiveAux p A s e C σ τ z).differentiableAt

theorem deriv_collectiveAux {N q : ℕ} (C : FeldmanIndex N q m → ℤ) (σ : ℕ) (τ : Fin d → ℕ) :
    deriv (collectiveAux p A s e N q C σ τ) = fun z =>
      ((σ : ℂ) + 1) * collectiveAux p A s e N q C (σ + 1) τ z +
        ∑ j : Fin d, (Real.log (p (e j)) : ℂ) *
          collectiveAux p A s e N q C σ (τ + Pi.single j 1) z := by
  funext z
  exact (hasDerivAt_collectiveAux p A s e C σ τ z).deriv


/-- **Derivatives along the diagonal.** -/
theorem norm_iteratedDeriv_collectiveAux_le (hp : ∀ j, 1 ≤ p j) {N q : ℕ}
    (C : FeldmanIndex N q m → ℤ) {z : ℂ} {n : ℕ} {β : ℝ}
    (hβ : ∀ σ (τ : Fin d → ℕ), σ + ∑ j, τ j ≤ n → ‖collectiveAux p A s e N q C σ τ z‖ ≤ β) :
    ∀ t σ (τ : Fin d → ℕ), σ + ∑ j, τ j + t ≤ n →
      ‖iteratedDeriv t (collectiveAux p A s e N q C σ τ) z‖ ≤ ((n : ℝ) + collectiveFreeLogSum p e) ^ t * β := by
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg _) (hβ 0 0 (by simp))
  have hW := collectiveFreeLogSum_nonneg p e hp
  intro t
  induction t with
  | zero =>
      intro σ τ h
      simpa using hβ σ τ (by omega)
  | succ t ih =>
      intro σ τ h
      have hd := differentiable_collectiveAux p A s e C
      have hcd : ∀ σ' τ' (c : ℂ), ContDiffAt ℂ t (fun w => c * collectiveAux p A s e N q C σ' τ' w) z :=
        fun σ' τ' c => (Differentiable.contDiff ((hd σ' τ').const_mul c)).contDiffAt
      rw [iteratedDeriv_succ', deriv_collectiveAux, iteratedDeriv_fun_add (hcd _ _ _)
        (ContDiff.sum fun j _ => Differentiable.contDiff ((hd _ _).const_mul _)).contDiffAt,
        iteratedDeriv_fun_sum fun j _ => hcd _ _ _, iteratedDeriv_const_mul_field]
      simp only [iteratedDeriv_const_mul_field]
      have h1 := ih (σ + 1) τ (by omega)
      have h2 : ∀ j : Fin d, ‖iteratedDeriv t (collectiveAux p A s e N q C σ (τ + Pi.single j 1)) z‖ ≤
          ((n : ℝ) + collectiveFreeLogSum p e) ^ t * β := fun j =>
        ih σ (τ + Pi.single j 1) (by rw [sum_add_piSingle]; omega)
      have hσn : ((σ : ℝ) + 1) ≤ n := by exact_mod_cast (show σ + 1 ≤ n by omega)
      have hpow : 0 ≤ ((n : ℝ) + collectiveFreeLogSum p e) ^ t * β := by positivity
      calc ‖((σ : ℂ) + 1) * iteratedDeriv t (collectiveAux p A s e N q C (σ + 1) τ) z +
            ∑ j : Fin d, (Real.log (p (e j)) : ℂ) *
              iteratedDeriv t (collectiveAux p A s e N q C σ (τ + Pi.single j 1)) z‖
          ≤ ((σ : ℝ) + 1) * (((n : ℝ) + collectiveFreeLogSum p e) ^ t * β) +
              ∑ j : Fin d, Real.log (p (e j)) * (((n : ℝ) + collectiveFreeLogSum p e) ^ t * β) := by
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_mul]
              refine mul_le_mul ?_ h1 (norm_nonneg _) (by positivity)
              rw [show ((σ : ℂ) + 1) = ((σ + 1 : ℕ) : ℂ) by push_cast; ring,
                Complex.norm_natCast]
              push_cast
              exact le_rfl
            · refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp _))]
              exact mul_le_mul_of_nonneg_left (h2 j) (Real.log_nonneg (by exact_mod_cast hp _))
        _ = ((σ : ℝ) + 1 + collectiveFreeLogSum p e) * (((n : ℝ) + collectiveFreeLogSum p e) ^ t * β) := by
            rw [← sum_mul, collectiveFreeLogSum]
            ring
        _ ≤ ((n : ℝ) + collectiveFreeLogSum p e) * (((n : ℝ) + collectiveFreeLogSum p e) ^ t * β) :=
            mul_le_mul_of_nonneg_right (by linarith) hpow
        _ = ((n : ℝ) + collectiveFreeLogSum p e) ^ (t + 1) * β := by ring


/-- Injective free coordinates have no more logarithmic mass than the full family. -/
theorem collectiveFreeLogSum_le_total (hp : ∀ j, 1 ≤ p j) (he : Function.Injective e) :
    collectiveFreeLogSum p e ≤ totalLogSum p := by
  classical
  rw [collectiveFreeLogSum, ← Finset.sum_image (f := fun j => Real.log (p j))
    (s := univ) (fun i _ j _ h => he h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun j _ _ => Real.log_nonneg (by exact_mod_cast hp j))

/-- The normalized pivot forms measure the perturbation of every frequency. -/
def collectiveFormDefect : ℝ :=
  ∑ i, |(∑ a, ((A.submatrix id s).adjugate i a : ℝ) *
    (∑ j, (A a j : ℝ) * Real.log (p j))) / ((A.submatrix id s).det : ℝ)|

theorem collectiveFormDefect_nonneg : 0 ≤ collectiveFormDefect p A s :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- The free-coordinate frequency is the full frequency minus the pivot-form error. -/
theorem collectiveFreq_eq (he : Function.Injective e)
    (hcover : ∀ j, (∃ i, s i = j) ∨ ∃ i, e i = j)
    (hdet : (A.submatrix id s).det ≠ 0) (l : Fin (m + 1) → ℕ) :
    collectiveFreq p A s e l = trueFreq p l -
      ∑ i, (l (s i) : ℝ) * ((∑ a, ((A.submatrix id s).adjugate i a : ℝ) *
        (∑ j, (A a j : ℝ) * Real.log (p j))) / ((A.submatrix id s).det : ℝ)) := by
  classical
  have hsum : collectiveFreq p A s e l =
      ∑ j, ((collectiveGamma A s (fun i => (l i : ℤ)) j : ℝ) /
        ((A.submatrix id s).det : ℝ)) * Real.log (p j) := by
    rw [collectiveFreq, ← Finset.sum_image
      (f := fun j => ((collectiveGamma A s (fun i => (l i : ℤ)) j : ℝ) /
        ((A.submatrix id s).det : ℝ)) * Real.log (p j))
      (s := univ) (fun i _ j _ h => he h)]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j hj hnot
    rcases hcover j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [collectiveGamma_pivot, Int.cast_zero, zero_div, zero_mul]
    · exact False.elim (hnot (Finset.mem_image.mpr ⟨i, mem_univ _, rfl⟩))
  rw [hsum, collectiveFrequency_defect A s hdet]
  simp only [Int.cast_natCast, trueFreq, Finset.sum_div, mul_div_assoc]

/-- A whole exponent box has perturbation at most its side length times the pivot defect. -/
theorem abs_collectiveFreq_sub_trueFreq_le (he : Function.Injective e)
    (hcover : ∀ j, (∃ i, s i = j) ∨ ∃ i, e i = j)
    (hdet : (A.submatrix id s).det ≠ 0) {q : ℕ}
    (l : Fin (m + 1) → ℕ) (hl : ∀ i, l i < q) :
    |collectiveFreq p A s e l - trueFreq p l| ≤ q * collectiveFormDefect p A s := by
  rw [collectiveFreq_eq p A s e he hcover hdet]
  rw [sub_sub_cancel_left, abs_neg, collectiveFormDefect, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (hl (s i)).le) (abs_nonneg _)

theorem norm_collectiveGammaWeight_le (hdet : (A.submatrix id s).det ≠ 0)
    (hmax : ∀ i j, |(A.submatrix id s).cramer (fun h => A h j) i| ≤
      |(A.submatrix id s).det|) {q : ℕ}
    (l : Fin (m + 1) → ℕ) (hl : ∀ i, l i < q) (τ : Fin d → ℕ) :
    ‖collectiveGammaWeight A s e l τ‖ ≤ ((r + 1 : ℝ) * q) ^ (∑ j, τ j) := by
  rw [collectiveGammaWeight, norm_prod, ← prod_pow_eq_pow_sum]
  refine prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => ?_
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_div, Complex.norm_intCast, Complex.norm_intCast, ← abs_div]
  exact collectiveGamma_div_bound A s hdet hmax (Nat.cast_nonneg q)
    (fun i => (l i : ℤ)) (fun i => by
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (hl i).le) (e j)

theorem abs_collectiveFreq_le (hdet : (A.submatrix id s).det ≠ 0)
    (hmax : ∀ i j, |(A.submatrix id s).cramer (fun h => A h j) i| ≤
      |(A.submatrix id s).det|) (hp : ∀ j, 1 ≤ p j) {q : ℕ}
    (l : Fin (m + 1) → ℕ) (hl : ∀ i, l i < q) :
    |collectiveFreq p A s e l| ≤ (r + 1 : ℝ) * q * collectiveFreeLogSum p e := by
  rw [collectiveFreq, collectiveFreeLogSum, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  have hlog : 0 ≤ Real.log (p (e j)) := Real.log_nonneg (by exact_mod_cast hp _)
  rw [abs_mul, abs_of_nonneg hlog]
  apply mul_le_mul_of_nonneg_right _ hlog
  exact collectiveGamma_div_bound A s hdet hmax (Nat.cast_nonneg q)
    (fun i => (l i : ℤ)) (fun i => by
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (hl i).le) (e j)


/-- **Growth of the auxiliary function.** -/
theorem norm_collectiveAux_le (hdet : (A.submatrix id s).det ≠ 0)
    (hmax : ∀ i j, |(A.submatrix id s).cramer (fun h => A h j) i| ≤ |(A.submatrix id s).det|)
    (hp : ∀ j, 1 ≤ p j) {N q : ℕ} (C : FeldmanIndex N q m → ℤ) {Cmax : ℝ}
    (hC : ∀ kl, |(C kl : ℝ)| ≤ Cmax) (σ : ℕ) (τ : Fin d → ℕ) (w : ℂ) :
    ‖collectiveAux p A s e N q C σ τ w‖ ≤
      ((N + 1) * q ^ (m + 1) : ℕ) * Cmax * (2 ^ N * (‖w‖ + N + 1) ^ N) *
        ((r + 1 : ℝ) * q : ℝ) ^ (∑ j, τ j) * Real.exp (‖w‖ * ((r + 1 : ℝ) * q * collectiveFreeLogSum p e)) := by
  have hcard : Fintype.card (FeldmanIndex N q m) = (N + 1) * q ^ (m + 1) := by
    simp [FeldmanIndex, Fintype.card_prod, Fintype.card_pi]
  rw [collectiveAux]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ kl : FeldmanIndex N q m,
      ‖(C kl : ℂ) * feldmanJet N kl.1 σ w * collectiveGammaWeight A s e kl.expo τ *
          Complex.exp (w * (collectiveFreq p A s e kl.expo : ℂ))‖ ≤
        Cmax * (2 ^ N * (‖w‖ + N + 1) ^ N) * ((r + 1 : ℝ) * q : ℝ) ^ (∑ j, τ j) *
          Real.exp (‖w‖ * ((r + 1 : ℝ) * q * collectiveFreeLogSum p e)) := by
    intro kl
    rw [norm_mul, norm_mul, norm_mul]
    have hCm : 0 ≤ Cmax := (abs_nonneg _).trans (hC kl)
    have h1 : ‖((C kl : ℤ) : ℂ)‖ ≤ Cmax := by
      rw [Complex.norm_intCast]
      exact hC kl
    have h2 := norm_feldmanJet_le (Nat.lt_succ_iff.mp kl.1.isLt) σ w
    have h3 := norm_collectiveGammaWeight_le A s e hdet hmax kl.expo (expo_lt kl) τ
    have h4 : ‖Complex.exp (w * (collectiveFreq p A s e kl.expo : ℂ))‖ ≤
        Real.exp (‖w‖ * ((r + 1 : ℝ) * q * collectiveFreeLogSum p e)) := by
      refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (abs_collectiveFreq_le p A s e hdet hmax hp kl.expo (expo_lt kl))
        (norm_nonneg _)
    gcongr
  refine (sum_le_sum fun kl _ => hterm kl).trans (le_of_eq ?_)
  rw [sum_const, card_univ, hcard, nsmul_eq_mul]
  ring

/-- The analytic auxiliary differs from its arithmetic companion only by
an explicitly controlled frequency perturbation. -/
theorem norm_collectiveAux_sub_true_le (hdet : (A.submatrix id s).det ≠ 0)
    (hmax : ∀ i j, |(A.submatrix id s).cramer (fun h => A h j) i| ≤ |(A.submatrix id s).det|)
    (he : Function.Injective e) (hcover : ∀ j, (∃ i, s i = j) ∨ ∃ i, e i = j)
    (hp : ∀ j, 1 ≤ p j) {N q : ℕ} (C : FeldmanIndex N q m → ℤ) {Cmax : ℝ}
    (hC : ∀ kl, |(C kl : ℝ)| ≤ Cmax) (σ : ℕ) (τ : Fin d → ℕ) {z : ℂ}
    (hz : ‖z‖ * q * collectiveFormDefect p A s ≤ 1) :
    ‖collectiveAux p A s e N q C σ τ z - collectiveTrueAux p A s e N q C σ τ z‖ ≤
      ((N + 1) * q ^ (m + 1) : ℕ) * Cmax * (2 ^ N * (‖z‖ + N + 1) ^ N) *
        ((r + 1 : ℝ) * q) ^ (∑ j, τ j) * Real.exp (‖z‖ * (q * totalLogSum p)) *
          (2 * (‖z‖ * q * collectiveFormDefect p A s)) := by
  rw [collectiveAux, collectiveTrueAux, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ kl : FeldmanIndex N q m,
      ‖(C kl : ℂ) * feldmanJet N kl.1 σ z * collectiveGammaWeight A s e kl.expo τ *
            Complex.exp (z * (collectiveFreq p A s e kl.expo : ℂ)) -
          (C kl : ℂ) * feldmanJet N kl.1 σ z * collectiveGammaWeight A s e kl.expo τ *
            Complex.exp (z * (trueFreq p kl.expo : ℂ))‖ ≤
        Cmax * (2 ^ N * (‖z‖ + N + 1) ^ N) * ((r + 1 : ℝ) * q) ^ (∑ j, τ j) *
          Real.exp (‖z‖ * (q * totalLogSum p)) * (2 * (‖z‖ * q * collectiveFormDefect p A s)) := by
    intro kl
    rw [← mul_sub, norm_mul, norm_mul, norm_mul]
    have hCm : 0 ≤ Cmax := (abs_nonneg _).trans (hC kl)
    have h1 : ‖((C kl : ℤ) : ℂ)‖ ≤ Cmax := by rw [Complex.norm_intCast]; exact hC kl
    have h2 := norm_feldmanJet_le (Nat.lt_succ_iff.mp kl.1.isLt) σ z
    have h3 := norm_collectiveGammaWeight_le A s e hdet hmax kl.expo (expo_lt kl) τ
    have hsplit : Complex.exp (z * (collectiveFreq p A s e kl.expo : ℂ)) -
        Complex.exp (z * (trueFreq p kl.expo : ℂ)) =
          Complex.exp (z * (trueFreq p kl.expo : ℂ)) *
            (Complex.exp (z * ((collectiveFreq p A s e kl.expo - trueFreq p kl.expo : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      push_cast
      ring_nf
    have hsmall : ‖z * ((collectiveFreq p A s e kl.expo - trueFreq p kl.expo : ℝ) : ℂ)‖ ≤
        ‖z‖ * q * collectiveFormDefect p A s := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (abs_collectiveFreq_sub_trueFreq_le p A s e he hcover hdet kl.expo (expo_lt kl))
        (norm_nonneg z)
    have h4 : ‖Complex.exp (z * (collectiveFreq p A s e kl.expo : ℂ)) -
        Complex.exp (z * (trueFreq p kl.expo : ℂ))‖ ≤
          Real.exp (‖z‖ * (q * totalLogSum p)) * (2 * (‖z‖ * q * collectiveFormDefect p A s)) := by
      rw [hsplit, norm_mul]
      refine mul_le_mul ?_ ((Complex.norm_exp_sub_one_le (hsmall.trans hz)).trans
        (by linarith only [hsmall])) (norm_nonneg _) (by positivity)
      refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [trueFreq, totalLogSum, mul_sum]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
      have hlog : 0 ≤ Real.log (p j) := Real.log_nonneg (by exact_mod_cast hp _)
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hlog]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (expo_lt kl j).le) hlog
    rw [mul_assoc _ (Real.exp _) _]
    gcongr
  refine (sum_le_sum fun kl _ => hterm kl).trans (le_of_eq ?_)
  rw [sum_const, card_univ, card_feldmanIndex, nsmul_eq_mul]
  ring


/-- Enlarge only the analytic majorant; keep the actual coefficient box `q`. -/
theorem norm_collectiveAux_le_growth (hdet : (A.submatrix id s).det ≠ 0)
    (hmax : ∀ i j, |(A.submatrix id s).cramer (fun h => A h j) i| ≤ |(A.submatrix id s).det|)
    (hp : ∀ j, 1 ≤ p j) {N q Q : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ Q)
    (hrQ : (r + 1) * q ≤ 2 * Q) (C : FeldmanIndex N q m → ℤ)
    {Cmax : ℝ} (hC : ∀ kl, |(C kl : ℝ)| ≤ Cmax) (hCmax : 0 ≤ Cmax)
    {T σ : ℕ} {τ : Fin d → ℕ} (hτ : ∑ j, τ j ≤ T)
    {ρ : ℝ} {w : ℂ} (hw : ‖w‖ = ρ) :
    ‖collectiveAux p A s e N q C σ τ w‖ ≤
      feldmanGrowthBound m N Q T Cmax (collectiveFreeLogSum p e) ρ := by
  have hW := collectiveFreeLogSum_nonneg p e hp
  have hρ : 0 ≤ ρ := hw ▸ norm_nonneg w
  have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hrQR : (r + 1 : ℝ) * q ≤ 2 * Q := by exact_mod_cast hrQ
  have hQ1 : (1 : ℝ) ≤ 2 * Q := by exact_mod_cast (show 1 ≤ 2 * Q by omega)
  have hpw : ((r + 1 : ℝ) * q) ^ (∑ j, τ j) ≤ (2 * Q : ℝ) ^ T :=
    (pow_le_pow_left₀ (by positivity) hrQR _).trans (pow_le_pow_right₀ hQ1 hτ)
  have hcard : (N + 1) * q ^ (m + 1) ≤ (N + 1) * Q ^ (m + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqQ _)
  have hcardR : (((N + 1) * q ^ (m + 1) : ℕ) : ℝ) ≤ ((N + 1) * Q ^ (m + 1) : ℕ) :=
    by exact_mod_cast hcard
  refine (norm_collectiveAux_le p A s e hdet hmax hp C hC σ τ w).trans ?_
  rw [hw]
  unfold feldmanGrowthBound
  gcongr

/-- Uniform comparison with the true companion on a disc, with an enlarged
analytic box but the original coefficient set. -/
theorem norm_collectiveAux_sub_le (hdet : (A.submatrix id s).det ≠ 0)
    (hmax : ∀ i j, |(A.submatrix id s).cramer (fun h => A h j) i| ≤ |(A.submatrix id s).det|)
    (he : Function.Injective e) (hcover : ∀ j, (∃ i, s i = j) ∨ ∃ i, e i = j)
    (hp : ∀ j, 1 ≤ p j) {N q Q : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ Q)
    (hrQ : (r + 1) * q ≤ 2 * Q) (C : FeldmanIndex N q m → ℤ)
    {Cmax : ℝ} (hC : ∀ kl, |(C kl : ℝ)| ≤ Cmax) (hCmax : 0 ≤ Cmax) {ρ : ℝ}
    (hΛ : ρ * Q * collectiveFormDefect p A s ≤ 1) {T σ : ℕ} {τ : Fin d → ℕ}
    (hτ : ∑ j, τ j ≤ T) {z : ℂ} (hz : ‖z‖ ≤ ρ) :
    ‖collectiveAux p A s e N q C σ τ z - collectiveTrueAux p A s e N q C σ τ z‖ ≤
      feldmanErrorBound m N Q T Cmax (totalLogSum p) ρ (collectiveFormDefect p A s) := by
  have hW := totalLogSum_nonneg p hp
  have hlam := collectiveFormDefect_nonneg p A s
  have hρ : 0 ≤ ρ := (norm_nonneg z).trans hz
  have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hrQR : (r + 1 : ℝ) * q ≤ 2 * Q := by exact_mod_cast hrQ
  have hQ1 : (1 : ℝ) ≤ 2 * Q := by exact_mod_cast (show 1 ≤ 2 * Q by omega)
  have hpw : ((r + 1 : ℝ) * q) ^ (∑ j, τ j) ≤ (2 * Q : ℝ) ^ T :=
    (pow_le_pow_left₀ (by positivity) hrQR _).trans (pow_le_pow_right₀ hQ1 hτ)
  have hcard : (N + 1) * q ^ (m + 1) ≤ (N + 1) * Q ^ (m + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqQ _)
  have hcardR : (((N + 1) * q ^ (m + 1) : ℕ) : ℝ) ≤ ((N + 1) * Q ^ (m + 1) : ℕ) :=
    by exact_mod_cast hcard
  have hzΛ : ‖z‖ * q * collectiveFormDefect p A s ≤ 1 :=
    le_trans (by gcongr) hΛ
  refine (norm_collectiveAux_sub_true_le p A s e hdet hmax he hcover hp C hC σ τ hzΛ).trans ?_
  unfold feldmanErrorBound
  rw [abs_of_nonneg hlam]
  gcongr

/-- An arithmetic companion smaller than its cleared integral unit is zero. -/
theorem collectiveTrueAux_eq_zero_of_small (hp : ∀ j, 1 ≤ p j)
    (hdet : (A.submatrix id s).det ≠ 0) {N q S : ℕ}
    (C : FeldmanIndex N q m → ℤ) {σ T : ℕ} (hσS : σ < S)
    {τ : Fin d → ℕ} (hτ : ∑ j, τ j ≤ T) (x : ℕ)
    (hsmall : |((A.submatrix id s).det : ℝ)| ^ T *
      ‖collectiveTrueAux p A s e N q C σ τ (x : ℂ)‖ < feldmanDivisor (N + 1) S) :
    collectiveTrueAux p A s e N q C σ τ (x : ℂ) = 0 := by
  have hrel := det_pow_mul_collectiveTrueAux_natCast p hp A s e hdet C hσS τ x
  have hF : (0 : ℝ) < feldmanDivisor (N + 1) S := by exact_mod_cast feldmanDivisor_pos _ _
  have hD1 : (1 : ℝ) ≤ |((A.submatrix id s).det : ℝ)| := by
    have h := abs_pos.mpr hdet
    have : (1 : ℤ) ≤ |(A.submatrix id s).det| := by omega
    exact_mod_cast this
  let J : ℤ := ∑ kl, collectiveJetCoeff p A s e N q S σ τ x kl * C kl
  have hJ : J = 0 := by
    have hnorm := congrArg norm hrel
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_intCast, Complex.norm_natCast,
      Complex.norm_intCast] at hnorm
    have hle : |((A.submatrix id s).det : ℝ)| ^ (∑ j, τ j) *
        ‖collectiveTrueAux p A s e N q C σ τ (x : ℂ)‖ ≤
        |((A.submatrix id s).det : ℝ)| ^ T * ‖collectiveTrueAux p A s e N q C σ τ (x : ℂ)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD1 hτ) (norm_nonneg _)
    have hlt : (feldmanDivisor (N + 1) S : ℝ) * |(J : ℝ)| < feldmanDivisor (N + 1) S := by
      rw [← hnorm]
      exact hle.trans_lt hsmall
    have habs : |(J : ℝ)| < 1 := by nlinarith only [hF, hlt]
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast habs)
  change ((A.submatrix id s).det : ℂ) ^ (∑ j, τ j) * _ = _ * (J : ℂ) at hrel
  rw [hJ, Int.cast_zero, mul_zero] at hrel
  exact (mul_eq_zero.mp hrel).resolve_left (pow_ne_zero _ (by exact_mod_cast hdet))

/-- **One extrapolation step.** -/
theorem collective_step (hp : ∀ j, 1 ≤ p j) (hdet : (A.submatrix id s).det ≠ 0)
    (hmax : ∀ i j, |(A.submatrix id s).cramer (fun h => A h j) i| ≤ |(A.submatrix id s).det|)
    (he : Function.Injective e) (hcover : ∀ j, (∃ i, s i = j) ∨ ∃ i, e i = j)
    {N q Q S : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ Q) (hrQ : (r + 1) * q ≤ 2 * Q) (C : FeldmanIndex N q m → ℤ)
    {Cmax : ℝ} (hC : ∀ kl, |(C kl : ℝ)| ≤ Cmax) (hCmax : 0 ≤ Cmax) {X T M : ℕ} (hX : 1 ≤ X)
    (hTS : T ≤ S) (hΛ : 8 * (X : ℝ) * Q * collectiveFormDefect p A s ≤ 1)
    (hzero : ∀ x < X, ∀ σ (τ : Fin d → ℕ), σ + ∑ j, τ j < T →
      collectiveTrueAux p A s e N q C σ τ (x : ℂ) = 0)
    (hgain : |((A.submatrix id s).det : ℝ)| ^ T * feldmanStepBound m N Q T X M Cmax (collectiveFreeLogSum p e)
      (totalLogSum p) (collectiveFormDefect p A s) < feldmanDivisor (N + 1) S) :
    ∀ x < 2 * X, ∀ σ (τ : Fin d → ℕ), σ + ∑ j, τ j + M < T →
      collectiveTrueAux p A s e N q C σ τ (x : ℂ) = 0 := by
  intro x' hx' σ τ hστ
  set W := collectiveFreeLogSum p e with hWdef
  set Wt := totalLogSum p with hWtdef
  set lam := collectiveFormDefect p A s with hlamdef
  set ρ : ℝ := 8 * X with hρdef
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hW0 : 0 ≤ W := collectiveFreeLogSum_nonneg p e hp
  set β := feldmanErrorBound m N Q T Cmax Wt ρ lam with hβdef
  have hβ0 : 0 ≤ β := feldmanErrorBound_nonneg hCmax hρ0.le
  set ε := ((T : ℝ) + W) ^ M * β with hεdef
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have hρΛ : ρ * Q * lam ≤ 1 := by rw [hρdef]; exact hΛ
  -- the error on the disc
  have herr : ∀ σ' (τ' : Fin d → ℕ), ∑ j, τ' j ≤ T → ∀ z : ℂ, ‖z‖ ≤ ρ →
      ‖collectiveAux p A s e N q C σ' τ' z - collectiveTrueAux p A s e N q C σ' τ' z‖ ≤ β :=
    fun σ' τ' hτ' z hz => norm_collectiveAux_sub_le p A s e hdet hmax he hcover hp hq hqQ hrQ C hC hCmax hρΛ hτ' hz
  have hT1 : 1 ≤ T := by omega
  -- the values at the nodes
  have hnode : ∀ x < X, ∀ σ' (τ' : Fin d → ℕ), σ' + ∑ j, τ' j ≤ T - 1 →
      ‖collectiveAux p A s e N q C σ' τ' (x : ℂ)‖ ≤ β := by
    intro x hx σ' τ' h
    have h0 := hzero x hx σ' τ' (by omega)
    have hxρ : ‖(x : ℂ)‖ ≤ ρ := by
      rw [Complex.norm_natCast, hρdef]
      have : (x : ℝ) ≤ X := by exact_mod_cast hx.le
      linarith
    have := herr σ' τ' (by omega) (x : ℂ) hxρ
    rwa [h0, sub_zero] at this
  -- the jets at the nodes
  have hjet : ∀ x < X, ∀ t < M,
      ‖iteratedDeriv t (collectiveAux p A s e N q C σ τ) (x : ℂ)‖ ≤ ε := by
    intro x hx t ht
    have h := norm_iteratedDeriv_collectiveAux_le p A s e hp C (n := T - 1) (β := β)
      (fun σ' τ' h' => hnode x hx σ' τ' h') t σ τ (by omega)
    have hbase : ((T - 1 : ℕ) : ℝ) + W ≤ (T : ℝ) + W := by
      have : ((T - 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast Nat.sub_le T 1
      linarith
    have hT1' : (1 : ℝ) ≤ (T : ℝ) + W := by
      have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
      linarith
    calc _ ≤ (((T - 1 : ℕ) : ℝ) + W) ^ t * β := h
      _ ≤ ((T : ℝ) + W) ^ t * β :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase t) hβ0
      _ ≤ ((T : ℝ) + W) ^ M * β :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT1' ht.le) hβ0
  -- Hermite–Schwarz
  set f := collectiveAux p A s e N q C σ τ with hfdef
  have hf : Differentiable ℂ f := differentiable_collectiveAux p A s e C σ τ
  set Hb := integerHermiteBound X M ρ ε with hHbdef
  have hH : ∀ z : ℂ, ‖z‖ ≤ ρ → ‖hermiteCorrection f (natNodes X) M z‖ ≤ Hb :=
    fun z hz => norm_hermiteCorrection_natNodes_le hε0 hρ0.le hjet hz
  have hτT : ∑ j, τ j ≤ T := by omega
  set G := feldmanGrowthBound m N Q T Cmax W ρ with hGdef
  have hbd : ∀ w ∈ sphere (0 : ℂ) ρ, ‖f w - hermiteCorrection f (natNodes X) M w‖ ≤ G + Hb := by
    intro w hw
    have hw' : ‖w‖ = ρ := by simpa using hw
    refine (norm_sub_le _ _).trans (add_le_add ?_ (hH w hw'.le))
    exact norm_collectiveAux_le_growth p A s e hdet hmax hp hq hqQ hrQ C hC hCmax hτT hw'
  have hXρ : (X : ℝ) ≤ ρ := by rw [hρdef]; linarith
  have h7 : ρ - X = 7 * X := by rw [hρdef]; ring
  have hDpos : 0 < (ρ - X) ^ (M * X) := by rw [h7]; positivity
  have hDlow : ∀ w ∈ sphere (0 : ℂ) ρ, (ρ - X) ^ (M * X) ≤ ‖hermiteNodePoly (natNodes X) M w‖ :=
    fun w hw => le_norm_hermiteNodePoly_natNodes M hXρ (by simpa using hw)
  have hx'ρ : ‖(x' : ℂ)‖ ≤ ρ := by
    rw [Complex.norm_natCast, hρdef]
    have : (x' : ℝ) ≤ 2 * X := by exact_mod_cast hx'.le
    linarith
  have hschwarz := norm_le_hermiteSchwarz hf (natNodes X) M hρ0 hDpos hbd hDlow
    (z := (x' : ℂ)) (by simpa using hx'ρ)
  have hΩ : ‖hermiteNodePoly (natNodes X) M (x' : ℂ)‖ ≤ ((2 * X : ℕ) : ℝ) ^ (M * X) :=
    norm_hermiteNodePoly_natNodes_le (by omega) M hx'
  have hratio : ((2 * X : ℕ) : ℝ) ^ (M * X) / (ρ - X) ^ (M * X) = (2 / 7 : ℝ) ^ (M * X) := by
    rw [h7, ← div_pow]
    congr 1
    push_cast
    field_simp
  have hGH : 0 ≤ G + Hb := add_nonneg (feldmanGrowthBound_nonneg hCmax hρ0.le)
    (integerHermiteBound_nonneg X M hε0)
  have hfx : ‖f (x' : ℂ)‖ ≤ Hb + (2 / 7 : ℝ) ^ (M * X) * (G + Hb) := by
    refine hschwarz.trans (add_le_add (hH _ hx'ρ) ?_)
    calc ‖hermiteNodePoly (natNodes X) M (x' : ℂ)‖ * ((G + Hb) / (ρ - X) ^ (M * X))
        ≤ ((2 * X : ℕ) : ℝ) ^ (M * X) * ((G + Hb) / (ρ - X) ^ (M * X)) :=
          mul_le_mul_of_nonneg_right hΩ (div_nonneg hGH hDpos.le)
      _ = ((2 * X : ℕ) : ℝ) ^ (M * X) / (ρ - X) ^ (M * X) * (G + Hb) := by ring
      _ = (2 / 7 : ℝ) ^ (M * X) * (G + Hb) := by rw [hratio]
  -- the true value
  have hΦ : ‖collectiveTrueAux p A s e N q C σ τ (x' : ℂ)‖ ≤
      feldmanStepBound m N Q T X M Cmax W Wt lam := by
    have h1 := herr σ τ hτT (x' : ℂ) hx'ρ
    have h2 : ‖collectiveTrueAux p A s e N q C σ τ (x' : ℂ)‖ ≤ ‖f (x' : ℂ)‖ +
        ‖collectiveAux p A s e N q C σ τ (x' : ℂ) - collectiveTrueAux p A s e N q C σ τ (x' : ℂ)‖ := by
      have := norm_sub_le (f (x' : ℂ))
        (collectiveAux p A s e N q C σ τ (x' : ℂ) - collectiveTrueAux p A s e N q C σ τ (x' : ℂ))
      simpa [hfdef] using this
    unfold feldmanStepBound
    rw [← hρdef, ← hβdef, ← hεdef, ← hHbdef, ← hGdef]
    linarith
  have hσS : σ < S := by omega
  refine collectiveTrueAux_eq_zero_of_small p A s e hp hdet C hσS hτT x' ?_
  have hB0 : (0 : ℝ) ≤ |((A.submatrix id s).det : ℝ)| ^ T := by
    positivity
  exact (mul_le_mul_of_nonneg_left hΦ hB0).trans_lt hgain

/-- **The extrapolation.**  From vanishing at `x < X₀` for `σ + |τ| < T₀`, after `R` steps the true
auxiliary values vanish at `x < 2^R X₀` for `σ + |τ| < T₀ − RM`. -/
theorem collective_extrapolation (hp : ∀ j, 1 ≤ p j) (hdet : (A.submatrix id s).det ≠ 0)
    (hmax : ∀ i j, |(A.submatrix id s).cramer (fun h => A h j) i| ≤ |(A.submatrix id s).det|)
    (he : Function.Injective e) (hcover : ∀ j, (∃ i, s i = j) ∨ ∃ i, e i = j)
    {N q Q S : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ Q) (hrQ : (r + 1) * q ≤ 2 * Q) (C : FeldmanIndex N q m → ℤ)
    {Cmax : ℝ} (hC : ∀ kl, |(C kl : ℝ)| ≤ Cmax) (hCmax : 0 ≤ Cmax) {X₀ T₀ M R : ℕ}
    (hX₀ : 1 ≤ X₀) (hT₀S : T₀ ≤ S) (hRM : R * M < T₀)
    (hΛ : 8 * ((2 ^ R * X₀ : ℕ) : ℝ) * Q * collectiveFormDefect p A s ≤ 1)
    (h0 : ∀ x < X₀, ∀ σ (τ : Fin d → ℕ), σ + ∑ j, τ j < T₀ →
      collectiveTrueAux p A s e N q C σ τ (x : ℂ) = 0)
    (hgain : ∀ r < R, |((A.submatrix id s).det : ℝ)| ^ (T₀ - r * M) *
      feldmanStepBound m N Q (T₀ - r * M) (2 ^ r * X₀) M Cmax (collectiveFreeLogSum p e) (totalLogSum p)
        (collectiveFormDefect p A s) < feldmanDivisor (N + 1) S) :
    ∀ x < 2 ^ R * X₀, ∀ σ (τ : Fin d → ℕ), σ + ∑ j, τ j < T₀ - R * M →
      collectiveTrueAux p A s e N q C σ τ (x : ℂ) = 0 := by
  have hΛnn := collectiveFormDefect_nonneg p A s
  suffices H : ∀ r ≤ R, ∀ x < 2 ^ r * X₀, ∀ σ (τ : Fin d → ℕ), σ + ∑ j, τ j < T₀ - r * M →
      collectiveTrueAux p A s e N q C σ τ (x : ℂ) = 0 from H R le_rfl
  intro r
  induction r with
  | zero => intro _; simpa using h0
  | succ r ih =>
      intro hr x hx σ τ hστ
      have hrR : r < R := by omega
      have hXr : 1 ≤ 2 ^ r * X₀ := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hpow : 2 ^ r * X₀ ≤ 2 ^ R * X₀ :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hrR.le)
      have hΛr : 8 * ((2 ^ r * X₀ : ℕ) : ℝ) * Q * collectiveFormDefect p A s ≤ 1 := by
        refine le_trans ?_ hΛ
        have : ((2 ^ r * X₀ : ℕ) : ℝ) ≤ ((2 ^ R * X₀ : ℕ) : ℝ) := by exact_mod_cast hpow
        gcongr
      have hrM : r * M + M ≤ R * M := by
        have := Nat.mul_le_mul_right M (show r + 1 ≤ R by omega)
        linarith [Nat.succ_mul r M]
      have step := collective_step p A s e hp hdet hmax he hcover hq hqQ hrQ C hC hCmax (X := 2 ^ r * X₀) (T := T₀ - r * M)
        (M := M) hXr (by omega) (by exact_mod_cast hΛr) (ih (Nat.le_of_succ_le hr)) (hgain r hrR)
      refine step x (by rw [pow_succ] at hx; linarith) σ τ ?_
      have : (r + 1) * M = r * M + M := Nat.succ_mul r M
      omega


end GaloisForLFunctions.CollectiveDiophantineGeometry
