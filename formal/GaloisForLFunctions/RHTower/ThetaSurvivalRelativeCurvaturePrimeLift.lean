import GaloisForLFunctions.RHTower.ThetaSurvivalRelativeCurvatureReconstruction
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.RHTower.AsymmetricHeatDoubleSum
import GaloisForLFunctions.RHTower.SchattenLogResidueFiniteRankPerturbation

open Filter Topology BigOperators

namespace PrimeHodgeHistory

noncomputable section

theorem summable_sq_exitHazard : Summable fun n => exitHazard n ^ 2 := by
  have hmajor : Summable fun n : ℕ => 36 * (((n : ℝ) + 1) ^ (-2 : ℝ)) :=
    (_root_.RHTower.summable_nat_add_one_rpow_neg
      (by norm_num : (1 : ℝ) < 2)).mul_left 36
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_ hmajor
  intro n
  rw [exitHazard_formula]
  have hden : ((n : ℝ) + 1) ^ 2 ≤ (2 * (n : ℝ) + 9) ^ 2 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [sq_nonneg ((n : ℝ) + 1), sq_nonneg (2 * (n : ℝ) + 9)]
  have hpos : 0 < ((n : ℝ) + 1) := by positivity
  rw [show (6 / (((2 * n + 9 : ℕ) : ℝ))) ^ 2 =
      36 / (((2 * n + 9 : ℕ) : ℝ)) ^ 2 by ring]
  push_cast
  rw [Real.rpow_neg (by positivity : 0 ≤ (n : ℝ) + 1)]
  norm_num
  exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hpos) hden

theorem summable_sq_outgoingMetricWeight :
    Summable fun n => outgoingMetricWeight n ^ 2 := by
  rw [← summable_nat_add_iff 1]
  simpa [outgoingMetricWeight] using summable_sq_exitHazard

theorem summable_sq_relativeCurvatureWeight :
    Summable fun n => relativeCurvatureWeight n ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_
    (summable_relativeCurvatureWeight.mul_left (1 / 3))
  intro n
  nlinarith [relativeCurvatureWeight_pos n,
    relativeCurvatureWeight_le_one_third n]

end

end PrimeHodgeHistory

namespace RHTower

open ContinuousLinearMap
open scoped InnerProductSpace Matrix ComplexOrder

noncomputable section

/-- Reindex two history--prime coordinates into history-pair and prime-pair coordinates. -/
def historyPrimePairEquiv :
    (PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) ≃
      ((ℕ × ℕ) × (Nat.Primes × Nat.Primes)) where
  toFun ab := ((ab.1.1, ab.2.1), (ab.1.2, ab.2.2))
  invFun hp := ((hp.1.1, hp.2.1), (hp.1.2, hp.2.2))
  left_inv ab := by rcases ab with ⟨⟨n, p⟩, ⟨m, q⟩⟩; rfl
  right_inv hp := by rcases hp with ⟨⟨n, m⟩, ⟨p, q⟩⟩; rfl

/-- Block-diagonal history lift of the literal normalized prime Stokes kernel. -/
def historyStokesKernel (a : ℕ → ℝ) (d : ℝ)
    (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) : ℂ :=
  if ab.1.1 = ab.2.1 then
    (a ab.1.1 : ℂ) * normalizedStokesPrimeKernel d (ab.1.2, ab.2.2)
  else 0

theorem normalizedStokesPrimeKernel_isHS {d : ℝ} (hd : 0 < d) :
    HilbertSchmidt.IsHS (normalizedStokesPrimeKernel d) := by
  have h := (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd).smul
    ((gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ)⁻¹)
  convert h using 1
  funext pq
  simp [normalizedStokesPrimeKernel, div_eq_mul_inv, smul_eq_mul, mul_comm]

theorem toOperator_smul_kernel {I : Type*} (K : I × I → ℂ)
    (hK : HilbertSchmidt.IsHS K) (c : ℂ) :
    HilbertSchmidt.toOperator (hK.smul c) = c • HilbertSchmidt.toOperator hK := by
  ext f i
  rw [HilbertSchmidt.toOperator_apply, smul_apply]
  change (∑' j, (c * K (i, j)) * f j) = c * ∑' j, K (i, j) * f j
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

def normalizedStokesPrimeOperator {d : ℝ} (hd : 0 < d) :
    lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] lp (fun _ : Nat.Primes => ℂ) 2 :=
  HilbertSchmidt.toOperator (normalizedStokesPrimeKernel_isHS hd)

theorem normalizedStokesPrimeOperator_eq_smul_child {d : ℝ} (hd : 0 < d) :
    normalizedStokesPrimeOperator hd =
      ((gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ)⁻¹) •
        HilbertSchmidt.toOperator
          (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd) := by
  let c : ℂ :=
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ)⁻¹
  have hkernel : normalizedStokesPrimeKernel d =
      c • routePPrimitiveGammaJuliaStokesCofinalChildKernel d := by
    funext pq
    simp [normalizedStokesPrimeKernel, c, div_eq_mul_inv, smul_eq_mul, mul_comm]
  rw [normalizedStokesPrimeOperator]
  exact (HilbertSchmidt.toOperator_congr
    (normalizedStokesPrimeKernel_isHS hd)
    ((routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd).smul c)
    hkernel).trans
      (toOperator_smul_kernel _
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd) c)

theorem norm_le_traceNorm_of_memSchattenClass_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T) : ‖T‖ ≤ traceNorm H T := by
  have h := approxNumber_mul_succ_le_traceNorm_of_memSchattenClass_one hT 0
  simpa [approxNumber_zero_eq_norm] using h

theorem traceNorm_routePPrimitiveGammaJuliaStokesCofinalChildOperator
    {d : ℝ} (hd : 0 < d) :
    traceNorm (lp (fun _ : Nat.Primes => ℂ) 2)
      (HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd)) =
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d := by
  rw [traceNorm_eq_re_opTrace_of_isPositive
    (routePPrimitiveGammaJuliaStokesCofinalChildOperator_memSchattenClass_one hd)
    (routePPrimitiveGammaJuliaStokesCofinalChildOperator_isPositive hd),
    opTrace_routePPrimitiveGammaJuliaStokesCofinalChildOperator hd]
  simp

theorem norm_normalizedStokesPrimeOperator_le_one {d : ℝ} (hd : 0 < d) :
    ‖normalizedStokesPrimeOperator hd‖ ≤ 1 := by
  rw [normalizedStokesPrimeOperator_eq_smul_child hd, norm_smul]
  have hchild := norm_le_traceNorm_of_memSchattenClass_one
    (routePPrimitiveGammaJuliaStokesCofinalChildOperator_memSchattenClass_one hd)
  rw [traceNorm_routePPrimitiveGammaJuliaStokesCofinalChildOperator hd] at hchild
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd)]
  have hJ := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd
  calc
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)⁻¹ *
        ‖HilbertSchmidt.toOperator
          (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd)‖ ≤
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)⁻¹ *
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d := by
          gcongr
    _ = 1 := inv_mul_cancel₀ hJ.ne'

/-- Fixed-history prime slice of a history--prime square-summable vector. -/
def historyPrimeSlice (f : PrimeHodgeHistoryHilbert) (n : ℕ) :
    lp (fun _ : Nat.Primes => ℂ) 2 :=
  ⟨fun p => f (n, p), HilbertSchmidt.memℓp_of_sq (by
    have hf : Summable fun np : PrimeHodgeHistoryIndex => ‖f np‖ ^ 2 :=
      by
        refine ((lp.memℓp f).summable (by norm_num)).congr fun np => ?_
        rw [ENNReal.toReal_ofNat, ← Real.rpow_natCast]
        norm_num
    exact hf.comp_injective (by
      intro p q hpq
      exact congrArg Prod.snd hpq))⟩

@[simp] theorem historyPrimeSlice_apply (f : PrimeHodgeHistoryHilbert) (n : ℕ)
    (p : Nat.Primes) : historyPrimeSlice f n p = f (n, p) := rfl

theorem tsum_norm_sq_historyPrimeSlice (f : PrimeHodgeHistoryHilbert) :
    (∑' n, ‖historyPrimeSlice f n‖ ^ 2) = ‖f‖ ^ 2 := by
  have hf : Summable fun np : PrimeHodgeHistoryIndex => ‖f np‖ ^ 2 :=
    by
      refine ((lp.memℓp f).summable (by norm_num)).congr fun np => ?_
      rw [ENNReal.toReal_ofNat, ← Real.rpow_natCast]
      norm_num
  have hslice (n : ℕ) : ‖historyPrimeSlice f n‖ ^ 2 =
      ∑' p : Nat.Primes, ‖f (n, p)‖ ^ 2 := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : Nat.Primes => ℂ)
      (by norm_num) (historyPrimeSlice f n)
  calc
    (∑' n, ‖historyPrimeSlice f n‖ ^ 2) =
        ∑' n, ∑' p : Nat.Primes, ‖f (n, p)‖ ^ 2 :=
      tsum_congr hslice
    _ = ∑' np : PrimeHodgeHistoryIndex, ‖f np‖ ^ 2 := hf.tsum_prod.symm
    _ = ‖f‖ ^ 2 := by
      symm
      simpa using lp.norm_rpow_eq_tsum (p := 2)
        (E := fun _ : PrimeHodgeHistoryIndex => ℂ) (by norm_num) f

theorem summable_norm_sq_historyPrimeSlice (f : PrimeHodgeHistoryHilbert) :
    Summable fun n => ‖historyPrimeSlice f n‖ ^ 2 := by
  have hf : Summable fun np : PrimeHodgeHistoryIndex => ‖f np‖ ^ 2 := by
    refine ((lp.memℓp f).summable (by norm_num)).congr fun np => ?_
    rw [ENNReal.toReal_ofNat, ← Real.rpow_natCast]
    norm_num
  have hprod := hf.prod
  refine hprod.congr fun n => ?_
  symm
  simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : Nat.Primes => ℂ)
    (by norm_num) (historyPrimeSlice f n)

theorem historyStokesKernel_norm_sq_reindex
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (d : ℝ)
    (hp : ((ℕ × ℕ) × (Nat.Primes × Nat.Primes))) :
    ‖historyStokesKernel a d (historyPrimePairEquiv.symm hp)‖ ^ 2 =
      diagMatrix (fun n => a n ^ 2) hp.1 * ‖normalizedStokesPrimeKernel d hp.2‖ ^ 2 := by
  rcases hp with ⟨⟨n, m⟩, ⟨p, q⟩⟩
  by_cases h : n = m
  · subst m
    simp [historyPrimePairEquiv, historyStokesKernel, diagMatrix,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n)]
    ring
  · simp [historyPrimePairEquiv, historyStokesKernel, diagMatrix, h]

theorem historyStokesKernel_isHS
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ha2 : Summable fun n => a n ^ 2) {d : ℝ} (hd : 0 < d) :
    HilbertSchmidt.IsHS (historyStokesKernel a d) := by
  rw [HilbertSchmidt.IsHS]
  rw [← (historyPrimePairEquiv.symm.summable_iff)]
  have hh : Summable (diagMatrix fun n => a n ^ 2) := summable_diagMatrix ha2
  have hp : Summable fun pq => ‖normalizedStokesPrimeKernel d pq‖ ^ 2 :=
    normalizedStokesPrimeKernel_isHS hd
  exact (summable_mul_of_summable_norm hh.norm hp.norm).congr
    (fun x => (historyStokesKernel_norm_sq_reindex a ha d x).symm)

theorem historyStokesKernel_hsAdjoint (a : ℕ → ℝ) (d : ℝ) :
    HilbertSchmidt.hsAdjoint (historyStokesKernel a d) = historyStokesKernel a d := by
  funext ab
  rw [HilbertSchmidt.hsAdjoint]
  change star (if ab.2.1 = ab.1.1 then
      (a ab.2.1 : ℂ) * normalizedStokesPrimeKernel d (ab.2.2, ab.1.2)
    else 0) =
    (if ab.1.1 = ab.2.1 then
      (a ab.1.1 : ℂ) * normalizedStokesPrimeKernel d (ab.1.2, ab.2.2)
    else 0)
  by_cases h : ab.1.1 = ab.2.1
  · have hr : ab.2.1 = ab.1.1 := h.symm
    rw [if_pos h, if_pos hr, star_mul]
    have hprime := congrFun (normalizedStokesPrimeKernel_hsAdjoint d) (ab.1.2, ab.2.2)
    rw [show star (normalizedStokesPrimeKernel d (ab.2.2, ab.1.2)) =
        normalizedStokesPrimeKernel d (ab.1.2, ab.2.2) by
      simpa [HilbertSchmidt.hsAdjoint] using hprime]
    rw [← h]
    simp [mul_comm]
  · have hr : ab.2.1 ≠ ab.1.1 := fun hr => h hr.symm
    rw [if_neg h, if_neg hr, star_zero]

def historyStokesDiagonalWeight (a : ℕ → ℝ) (d : ℝ)
    (np : PrimeHodgeHistoryIndex) : ℝ :=
  a np.1 * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d np.2 /
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d

theorem historyStokesDiagonalWeight_pos
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) {d : ℝ} (hd : 0 < d)
    (np : PrimeHodgeHistoryIndex) : 0 < historyStokesDiagonalWeight a d np := by
  exact div_pos (mul_pos (ha np.1)
    (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd np.2))
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd)

theorem historyStokesKernel_diagonal
    (a : ℕ → ℝ) {d : ℝ} (hd : 0 < d) (np : PrimeHodgeHistoryIndex) :
    historyStokesKernel a d (np, np) = (historyStokesDiagonalWeight a d np : ℂ) := by
  rw [historyStokesKernel, if_pos rfl, normalizedStokesPrimeKernel,
    routePPrimitiveGammaJuliaStokesCofinalChildKernel_diagonal hd,
    historyStokesDiagonalWeight]
  push_cast
  ring

theorem historyStokesKernel_sameHistory_ne_zero
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) {d : ℝ} (hd : 0 < d)
    (n : ℕ) (p q : Nat.Primes) :
    historyStokesKernel a d ((n, p), (n, q)) ≠ 0 := by
  rw [historyStokesKernel, if_pos rfl, normalizedStokesPrimeKernel]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ha n).ne')
    (div_ne_zero (routePPrimitiveGammaJuliaStokesCofinalChildKernel_ne_zero hd p q)
      (Complex.ofReal_ne_zero.mpr
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).ne'))

def historyStokesOperator
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ha2 : Summable fun n => a n ^ 2) {d : ℝ} (hd : 0 < d) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  HilbertSchmidt.toOperator (historyStokesKernel_isHS a ha ha2 hd)

theorem historyStokesOperator_apply_coordinate
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ha2 : Summable fun n => a n ^ 2) {d : ℝ} (hd : 0 < d)
    (f : PrimeHodgeHistoryHilbert) (n : ℕ) (p : Nat.Primes) :
    historyStokesOperator a ha ha2 hd f (n, p) =
      (a n : ℂ) * (normalizedStokesPrimeOperator hd (historyPrimeSlice f n)) p := by
  change (∑' mq : PrimeHodgeHistoryIndex,
      historyStokesKernel a d ((n, p), mq) * f mq) = _
  let emb : Nat.Primes → PrimeHodgeHistoryIndex := fun q => (n, q)
  have hinj : Function.Injective emb := by
    intro q r hqr
    exact congrArg Prod.snd hqr
  have hsupp : Function.support (fun mq : PrimeHodgeHistoryIndex =>
      historyStokesKernel a d ((n, p), mq) * f mq) ⊆ Set.range emb := by
    intro mq hmq
    by_cases hhist : n = mq.1
    · exact ⟨mq.2, Prod.ext hhist rfl⟩
    · exfalso
      apply hmq
      simp [historyStokesKernel, hhist]
  rw [← Function.Injective.tsum_eq hinj hsupp]
  rw [normalizedStokesPrimeOperator, HilbertSchmidt.toOperator_apply]
  rw [← tsum_mul_left]
  exact tsum_congr fun q => by
    simp [emb, historyStokesKernel]
    ring

theorem historyPrimeSlice_historyStokesOperator
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ha2 : Summable fun n => a n ^ 2) {d : ℝ} (hd : 0 < d)
    (f : PrimeHodgeHistoryHilbert) (n : ℕ) :
    historyPrimeSlice (historyStokesOperator a ha ha2 hd f) n =
      (a n : ℂ) • normalizedStokesPrimeOperator hd (historyPrimeSlice f n) := by
  ext p
  rw [historyPrimeSlice_apply, historyStokesOperator_apply_coordinate]
  rfl

theorem norm_historyStokesOperator_apply_le
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ha2 : Summable fun n => a n ^ 2) {C : ℝ} (hC : 0 ≤ C)
    (haC : ∀ n, a n ≤ C) {d : ℝ} (hd : 0 < d)
    (f : PrimeHodgeHistoryHilbert) :
    ‖historyStokesOperator a ha ha2 hd f‖ ≤ C * ‖f‖ := by
  let T := historyStokesOperator a ha ha2 hd
  have hslice (n : ℕ) :
      ‖historyPrimeSlice (T f) n‖ ≤ C * ‖historyPrimeSlice f n‖ := by
    rw [show historyPrimeSlice (T f) n =
        (a n : ℂ) • normalizedStokesPrimeOperator hd (historyPrimeSlice f n) by
      exact historyPrimeSlice_historyStokesOperator a ha ha2 hd f n]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n)]
    calc
      a n * ‖normalizedStokesPrimeOperator hd (historyPrimeSlice f n)‖ ≤
          a n * (‖normalizedStokesPrimeOperator hd‖ * ‖historyPrimeSlice f n‖) := by
        exact mul_le_mul_of_nonneg_left
          ((normalizedStokesPrimeOperator hd).le_opNorm _) (ha n)
      _ ≤ a n * (1 * ‖historyPrimeSlice f n‖) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (norm_normalizedStokesPrimeOperator_le_one hd) (norm_nonneg _)) (ha n)
      _ ≤ C * ‖historyPrimeSlice f n‖ := by
        simpa using mul_le_mul_of_nonneg_right (haC n) (norm_nonneg _)
  have hterm (n : ℕ) : ‖historyPrimeSlice (T f) n‖ ^ 2 ≤
      C ^ 2 * ‖historyPrimeSlice f n‖ ^ 2 := by
    nlinarith [hslice n, norm_nonneg (historyPrimeSlice (T f) n),
      norm_nonneg (historyPrimeSlice f n)]
  have hsumOut := summable_norm_sq_historyPrimeSlice (T f)
  have hsumIn := summable_norm_sq_historyPrimeSlice f
  have hpow : ‖T f‖ ^ 2 ≤ (C * ‖f‖) ^ 2 := by
    rw [← tsum_norm_sq_historyPrimeSlice (T f)]
    calc
      (∑' n, ‖historyPrimeSlice (T f) n‖ ^ 2) ≤
          ∑' n, C ^ 2 * ‖historyPrimeSlice f n‖ ^ 2 :=
        Summable.tsum_le_tsum hterm hsumOut (hsumIn.mul_left (C ^ 2))
      _ = C ^ 2 * ∑' n, ‖historyPrimeSlice f n‖ ^ 2 := tsum_mul_left
      _ = C ^ 2 * ‖f‖ ^ 2 := by rw [tsum_norm_sq_historyPrimeSlice]
      _ = (C * ‖f‖) ^ 2 := by ring
  have hleft : 0 ≤ ‖T f‖ := norm_nonneg _
  have hright : 0 ≤ C * ‖f‖ := mul_nonneg hC (norm_nonneg _)
  nlinarith

theorem norm_historyStokesOperator_le
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ha2 : Summable fun n => a n ^ 2) {C : ℝ} (hC : 0 ≤ C)
    (haC : ∀ n, a n ≤ C) {d : ℝ} (hd : 0 < d) :
    ‖historyStokesOperator a ha ha2 hd‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  exact norm_historyStokesOperator_apply_le a ha ha2 hC haC hd

section FinitePositivity

open Matrix

variable {N : ℕ}

def historyStokesMaskDiagonal (a : ℕ → ℝ)
    (x : Fin N → PrimeHodgeHistoryIndex) (r : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => if (x i).1 = r then (Real.sqrt (a r) : ℂ) else 0

def historyStokesFiniteMatrix (a : ℕ → ℝ) (d : ℝ)
    (x : Fin N → PrimeHodgeHistoryIndex) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => historyStokesKernel a d (x i, x j)

theorem historyStokesMask_congruence_apply
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (d : ℝ)
    (x : Fin N → PrimeHodgeHistoryIndex) (r : ℕ) (i j : Fin N) :
    (Matrix.conjTranspose (historyStokesMaskDiagonal a x r) *
      normalizedStokesFiniteMatrix d x * historyStokesMaskDiagonal a x r) i j =
      if (x i).1 = r ∧ (x j).1 = r then
        a r * normalizedStokesFiniteMatrix d x i j else 0 := by
  have hself : Matrix.conjTranspose (historyStokesMaskDiagonal a x r) =
      historyStokesMaskDiagonal a x r := by
    ext u v
    by_cases huv : u = v
    · subst v
      rw [Matrix.conjTranspose_apply]
      simp only [historyStokesMaskDiagonal, Matrix.diagonal_apply_eq]
      by_cases hu : (x u).1 = r
      · rw [if_pos hu]
        simp
      · rw [if_neg hu, star_zero]
    · rw [Matrix.conjTranspose_apply]
      simp only [historyStokesMaskDiagonal, Matrix.diagonal_apply_ne _ huv,
        Matrix.diagonal_apply_ne _ (Ne.symm huv), star_zero]
  rw [hself, Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · by_cases hi : (x i).1 = r
      · by_cases hj : (x j).1 = r
        · simp only [historyStokesMaskDiagonal, hi, hj, if_true,
            Matrix.diagonal_apply_eq, true_and]
          let z : ℂ := normalizedStokesFiniteMatrix d x i j
          change ((Real.sqrt (a r) : ℝ) : ℂ) * z *
              ((Real.sqrt (a r) : ℝ) : ℂ) = ((a r : ℝ) : ℂ) * z
          rw [show ((a r : ℝ) : ℂ) =
              ((Real.sqrt (a r) : ℝ) : ℂ) * ((Real.sqrt (a r) : ℝ) : ℂ) by
            norm_cast
            simpa [pow_two] using (Real.sq_sqrt (ha r)).symm]
          ring
        · simp [historyStokesMaskDiagonal, hi, hj]
      · simp [historyStokesMaskDiagonal, hi]
    · intro k _ hki
      simp [historyStokesMaskDiagonal, Ne.symm hki]
    · simp
  · intro k _ hkj
    simp [historyStokesMaskDiagonal, hkj]
  · simp

theorem historyStokesFiniteMatrix_eq_sum_congruence
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (d : ℝ)
    (x : Fin N → PrimeHodgeHistoryIndex) :
    historyStokesFiniteMatrix a d x =
      ∑ r ∈ Finset.univ.image (fun i : Fin N => (x i).1),
        Matrix.conjTranspose (historyStokesMaskDiagonal a x r) *
          normalizedStokesFiniteMatrix d x * historyStokesMaskDiagonal a x r := by
  let S : Matrix (Fin N) (Fin N) ℂ :=
    ∑ r ∈ Finset.univ.image (fun i : Fin N => (x i).1),
      Matrix.conjTranspose (historyStokesMaskDiagonal a x r) *
        normalizedStokesFiniteMatrix d x * historyStokesMaskDiagonal a x r
  change historyStokesFiniteMatrix a d x = S
  apply Matrix.ext
  intro i j
  rw [historyStokesFiniteMatrix]
  rw [show S i j = ∑ r ∈ Finset.univ.image (fun k : Fin N => (x k).1),
      (Matrix.conjTranspose (historyStokesMaskDiagonal a x r) *
        normalizedStokesFiniteMatrix d x * historyStokesMaskDiagonal a x r) i j by
      dsimp only [S]
      exact matrix_finset_sum_apply _ _ i j]
  simp_rw [historyStokesMask_congruence_apply a ha]
  by_cases hij : (x i).1 = (x j).1
  · rw [historyStokesKernel, if_pos hij]
    rw [Finset.sum_eq_single (x i).1]
    · simp [hij, normalizedStokesFiniteMatrix]
    · intro r hr hne
      simp [Ne.symm hne]
    · simp
  · rw [historyStokesKernel, if_neg hij]
    rw [eq_comm]
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hi : (x i).1 = r
    · have hj : (x j).1 ≠ r := by
        intro hj
        exact hij (hi.trans hj.symm)
      simp [hi, hj]
    · simp [hi]

theorem historyStokesFiniteMatrix_posSemidef
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {d : ℝ} (hd : 0 < d)
    (x : Fin N → PrimeHodgeHistoryIndex) :
    (historyStokesFiniteMatrix a d x).PosSemidef := by
  rw [historyStokesFiniteMatrix_eq_sum_congruence a ha]
  exact Finset.sum_induction _ Matrix.PosSemidef
    (fun _ _ hx hy => hx.add hy) Matrix.PosSemidef.zero
    (fun r _ => (normalizedStokesFiniteMatrix_posSemidef hd x).conjTranspose_mul_mul_same
      (historyStokesMaskDiagonal a x r))

theorem historyStokesBlockMatrix_posSemidef
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {d : ℝ} (hd : 0 < d)
    (s : Finset PrimeHodgeHistoryIndex) :
    (HilbertSchmidt.blockMatrix (historyStokesKernel a d) s).PosSemidef := by
  let x : Fin s.card → PrimeHodgeHistoryIndex := fun i => (s.equivFin.symm i).1
  have hM : (historyStokesFiniteMatrix a d x).PosSemidef :=
    historyStokesFiniteMatrix_posSemidef a ha hd x
  have hsub := hM.submatrix s.equivFin
  have heq : HilbertSchmidt.blockMatrix (historyStokesKernel a d) s =
      (historyStokesFiniteMatrix a d x).submatrix s.equivFin s.equivFin := by
    ext i j
    rw [HilbertSchmidt.blockMatrix]
    change historyStokesKernel a d (i.1, j.1) =
      historyStokesFiniteMatrix a d x (s.equivFin i) (s.equivFin j)
    rw [historyStokesFiniteMatrix]
    simp [x]
  rwa [heq]

end FinitePositivity

theorem historyStokesOperator_isPositive
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ha2 : Summable fun n => a n ^ 2) {d : ℝ} (hd : 0 < d) :
    (historyStokesOperator a ha ha2 hd).IsPositive :=
  toOperator_isPositive_of_blockMatrix_posSemidef
    (historyStokesKernel_isHS a ha ha2 hd)
    (historyStokesKernel_hsAdjoint a d)
    (historyStokesBlockMatrix_posSemidef a ha hd)

theorem historyStokesOperator_isCompactOperator
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ha2 : Summable fun n => a n ^ 2) {d : ℝ} (hd : 0 < d) :
    IsCompactOperator (historyStokesOperator a ha ha2 hd) := by
  exact (HilbertSchmidt.isHilbertSchmidt_toOperator
    (historyStokesKernel_isHS a ha ha2 hd)).isCompactOperator

theorem inner_lpBasis_historyStokesOperator
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ha2 : Summable fun n => a n ^ 2) {d : ℝ} (hd : 0 < d)
    (np : PrimeHodgeHistoryIndex) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np)
      (historyStokesOperator a ha ha2 hd
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np)) =
      (historyStokesDiagonalWeight a d np : ℂ) := by
  exact (HilbertSchmidt.inner_lpBasis_toOperator
    (historyStokesKernel_isHS a ha ha2 hd) np).trans
      (historyStokesKernel_diagonal a hd np)

theorem summable_historyStokesDiagonalWeight
    (a : ℕ → ℝ) (ha : Summable a) {d : ℝ} (hd : 0 < d) :
    Summable (historyStokesDiagonalWeight a d) := by
  have hp := summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd
  have hprod : Summable (fun np : PrimeHodgeHistoryIndex =>
      a np.1 * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d np.2) :=
    summable_mul_of_summable_norm ha.norm hp.norm
  exact (hprod.div_const _).congr fun np => by
    rw [historyStokesDiagonalWeight]

theorem tsum_historyStokesDiagonalWeight
    (a : ℕ → ℝ) (ha : Summable a) {d : ℝ} (hd : 0 < d) :
    (∑' np, historyStokesDiagonalWeight a d np) = ∑' n, a n := by
  have hp := summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd
  have hfactor := tsum_mul_tsum_of_summable_norm ha.norm hp.norm
  rw [show historyStokesDiagonalWeight a d = fun np : PrimeHodgeHistoryIndex =>
      (a np.1 * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d np.2) /
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d by rfl]
  rw [tsum_div_const]
  rw [show (∑' np : PrimeHodgeHistoryIndex,
      a np.1 * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d np.2) =
      (∑' n, a n) *
        ∑' p, routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p by
          exact hfactor.symm]
  rw [tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd]
  field_simp [(gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).ne']

theorem summable_historyStokesOperator_diagonal
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a)
    (ha2 : Summable fun n => a n ^ 2) {d : ℝ} (hd : 0 < d) :
    Summable (fun np => inner ℂ
      (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np)
      (historyStokesOperator a ha0 ha2 hd
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np))) := by
  refine (Complex.summable_ofReal.mpr
    (summable_historyStokesDiagonalWeight a ha hd)).congr fun np => ?_
  exact (inner_lpBasis_historyStokesOperator a ha0 ha2 hd np).symm

theorem historyStokesOperator_memSchattenClass_one
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a)
    (ha2 : Summable fun n => a n ^ 2) {d : ℝ} (hd : 0 < d) :
    MemSchattenClass 1 (historyStokesOperator a ha0 ha2 hd) :=
  memSchattenClass_one_of_isPositive_of_summable_diagonal
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex)
    (historyStokesOperator_isPositive a ha0 ha2 hd)
    (summable_historyStokesOperator_diagonal a ha0 ha ha2 hd)

theorem opTrace_historyStokesOperator
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a)
    (ha2 : Summable fun n => a n ^ 2) {d : ℝ} (hd : 0 < d) :
    ContinuousLinearMap.opTrace (historyStokesOperator a ha0 ha2 hd) =
      (∑' n, a n : ℝ) := by
  rw [opTrace_eq_tsum_basis_of_isPositive_of_summable_diagonal
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex)
    (historyStokesOperator_isPositive a ha0 ha2 hd)
    (summable_historyStokesOperator_diagonal a ha0 ha ha2 hd)]
  rw [tsum_congr (fun np => inner_lpBasis_historyStokesOperator a ha0 ha2 hd np),
    ← Complex.ofReal_tsum, tsum_historyStokesDiagonalWeight a ha hd]

theorem traceNorm_historyStokesOperator
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a)
    (ha2 : Summable fun n => a n ^ 2) {d : ℝ} (hd : 0 < d) :
    traceNorm PrimeHodgeHistoryHilbert (historyStokesOperator a ha0 ha2 hd) =
      ∑' n, a n := by
  rw [traceNorm_eq_re_opTrace_of_isPositive
    (historyStokesOperator_memSchattenClass_one a ha0 ha ha2 hd)
    (historyStokesOperator_isPositive a ha0 ha2 hd),
    opTrace_historyStokesOperator a ha0 ha ha2 hd]
  simp

theorem historyStokesOperator_not_memSchattenClass_one
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (haSum : ¬ Summable a)
    (ha2 : Summable fun n => a n ^ 2) {d : ℝ} (hd : 0 < d) :
    ¬ MemSchattenClass 1 (historyStokesOperator a (fun n => (ha n).le) ha2 hd) := by
  intro h
  have hdiag := h.one_summable_norm_inner_diag_basis
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex)
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hinj : Function.Injective (fun n : ℕ => (n, p) : ℕ → PrimeHodgeHistoryIndex) := by
    intro n m hnm
    exact congrArg Prod.fst hnm
  have hsub := hdiag.comp_injective hinj
  have hc : 0 < routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p /
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d :=
    div_pos (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd p)
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd)
  apply haSum
  have hscaled : Summable fun n =>
      a n * (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p /
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d) := by
    refine hsub.congr fun n => ?_
    rw [Function.comp_apply,
      inner_lpBasis_historyStokesOperator a (fun n => (ha n).le) ha2 hd,
      historyStokesDiagonalWeight, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos]
    · ring
    · exact div_pos (mul_pos (ha n)
        (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd p))
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd)
  refine (hscaled.div_const
    (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p /
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)).congr fun n => ?_
  field_simp [hc.ne',
    (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd p).ne',
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).ne']

theorem tsum_historyStokesDiagonalWeight_prime
    (a : ℕ → ℝ) (n : ℕ) {d : ℝ} (hd : 0 < d) :
    (∑' p : Nat.Primes, historyStokesDiagonalWeight a d (n, p)) = a n := by
  rw [show (fun p : Nat.Primes => historyStokesDiagonalWeight a d (n, p)) =
      fun p => a n * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p /
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d by rfl]
  rw [tsum_div_const, tsum_mul_left,
    tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd]
  field_simp [(gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).ne']

/-- Prime-mixed incoming metric `A₋ ⊗ A_form`. -/
def primeHodgeHistoryIncomingPrimeMetric :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  historyStokesOperator PrimeHodgeHistory.exitHazard
    (fun n => (PrimeHodgeHistory.exitHazard_pos n).le)
    PrimeHodgeHistory.summable_sq_exitHazard zero_lt_one

/-- Prime-mixed outgoing metric `A₊ ⊗ A_form`. -/
def primeHodgeHistoryOutgoingPrimeMetric :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  historyStokesOperator PrimeHodgeHistory.outgoingMetricWeight
    (fun n => (PrimeHodgeHistory.outgoingMetricWeight_pos n).le)
    PrimeHodgeHistory.summable_sq_outgoingMetricWeight zero_lt_one

/-- Prime-mixed relative curvature `K ⊗ A_form`. -/
def primeHodgeHistoryRelativeCurvaturePrimeLift :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  historyStokesOperator PrimeHodgeHistory.relativeCurvatureWeight
    (fun n => (PrimeHodgeHistory.relativeCurvatureWeight_pos n).le)
    PrimeHodgeHistory.summable_sq_relativeCurvatureWeight zero_lt_one

theorem primeHodgeHistoryIncomingPrimeMetric_isPositive :
    primeHodgeHistoryIncomingPrimeMetric.IsPositive := by
  exact historyStokesOperator_isPositive PrimeHodgeHistory.exitHazard
    (fun n => (PrimeHodgeHistory.exitHazard_pos n).le)
    PrimeHodgeHistory.summable_sq_exitHazard zero_lt_one

theorem primeHodgeHistoryOutgoingPrimeMetric_isPositive :
    primeHodgeHistoryOutgoingPrimeMetric.IsPositive := by
  exact historyStokesOperator_isPositive PrimeHodgeHistory.outgoingMetricWeight
    (fun n => (PrimeHodgeHistory.outgoingMetricWeight_pos n).le)
    PrimeHodgeHistory.summable_sq_outgoingMetricWeight zero_lt_one

theorem primeHodgeHistoryRelativeCurvaturePrimeLift_isPositive :
    primeHodgeHistoryRelativeCurvaturePrimeLift.IsPositive := by
  exact historyStokesOperator_isPositive PrimeHodgeHistory.relativeCurvatureWeight
    (fun n => (PrimeHodgeHistory.relativeCurvatureWeight_pos n).le)
    PrimeHodgeHistory.summable_sq_relativeCurvatureWeight zero_lt_one

theorem primeHodgeHistoryIncomingPrimeMetric_isCompactOperator :
    IsCompactOperator primeHodgeHistoryIncomingPrimeMetric := by
  exact historyStokesOperator_isCompactOperator PrimeHodgeHistory.exitHazard
    (fun n => (PrimeHodgeHistory.exitHazard_pos n).le)
    PrimeHodgeHistory.summable_sq_exitHazard zero_lt_one

theorem primeHodgeHistoryOutgoingPrimeMetric_isCompactOperator :
    IsCompactOperator primeHodgeHistoryOutgoingPrimeMetric := by
  exact historyStokesOperator_isCompactOperator PrimeHodgeHistory.outgoingMetricWeight
    (fun n => (PrimeHodgeHistory.outgoingMetricWeight_pos n).le)
    PrimeHodgeHistory.summable_sq_outgoingMetricWeight zero_lt_one

theorem primeHodgeHistoryIncomingPrimeMetric_not_memSchattenClass_one :
    ¬ MemSchattenClass 1 primeHodgeHistoryIncomingPrimeMetric := by
  exact historyStokesOperator_not_memSchattenClass_one PrimeHodgeHistory.exitHazard
    PrimeHodgeHistory.exitHazard_pos PrimeHodgeHistory.not_summable_exitHazard
    PrimeHodgeHistory.summable_sq_exitHazard zero_lt_one

theorem primeHodgeHistoryOutgoingPrimeMetric_not_memSchattenClass_one :
    ¬ MemSchattenClass 1 primeHodgeHistoryOutgoingPrimeMetric := by
  exact historyStokesOperator_not_memSchattenClass_one PrimeHodgeHistory.outgoingMetricWeight
    PrimeHodgeHistory.outgoingMetricWeight_pos
    PrimeHodgeHistory.not_summable_outgoingMetricWeight
    PrimeHodgeHistory.summable_sq_outgoingMetricWeight zero_lt_one

theorem primeHodgeHistoryRelativeCurvaturePrimeLift_memSchattenClass_one :
    MemSchattenClass 1 primeHodgeHistoryRelativeCurvaturePrimeLift := by
  exact historyStokesOperator_memSchattenClass_one
    PrimeHodgeHistory.relativeCurvatureWeight
    (fun n => (PrimeHodgeHistory.relativeCurvatureWeight_pos n).le)
    PrimeHodgeHistory.summable_relativeCurvatureWeight
    PrimeHodgeHistory.summable_sq_relativeCurvatureWeight zero_lt_one

theorem opTrace_primeHodgeHistoryRelativeCurvaturePrimeLift :
    ContinuousLinearMap.opTrace primeHodgeHistoryRelativeCurvaturePrimeLift = 1 := by
  rw [show primeHodgeHistoryRelativeCurvaturePrimeLift =
      historyStokesOperator PrimeHodgeHistory.relativeCurvatureWeight
        (fun n => (PrimeHodgeHistory.relativeCurvatureWeight_pos n).le)
        PrimeHodgeHistory.summable_sq_relativeCurvatureWeight zero_lt_one by rfl]
  rw [opTrace_historyStokesOperator PrimeHodgeHistory.relativeCurvatureWeight
    (fun n => (PrimeHodgeHistory.relativeCurvatureWeight_pos n).le)
    PrimeHodgeHistory.summable_relativeCurvatureWeight
    PrimeHodgeHistory.summable_sq_relativeCurvatureWeight zero_lt_one,
    PrimeHodgeHistory.tsum_relativeCurvatureWeight]
  norm_num

theorem traceNorm_primeHodgeHistoryRelativeCurvaturePrimeLift :
    traceNorm PrimeHodgeHistoryHilbert primeHodgeHistoryRelativeCurvaturePrimeLift = 1 := by
  rw [traceNorm_eq_re_opTrace_of_isPositive
    primeHodgeHistoryRelativeCurvaturePrimeLift_memSchattenClass_one
    primeHodgeHistoryRelativeCurvaturePrimeLift_isPositive,
    opTrace_primeHodgeHistoryRelativeCurvaturePrimeLift]
  norm_num

theorem norm_primeHodgeHistoryRelativeCurvaturePrimeLift_le_one_third :
    ‖primeHodgeHistoryRelativeCurvaturePrimeLift‖ ≤ 1 / 3 := by
  exact norm_historyStokesOperator_le
    PrimeHodgeHistory.relativeCurvatureWeight
    (fun n => (PrimeHodgeHistory.relativeCurvatureWeight_pos n).le)
    PrimeHodgeHistory.summable_sq_relativeCurvatureWeight
    (by norm_num) PrimeHodgeHistory.relativeCurvatureWeight_le_one_third zero_lt_one

theorem primeHodgeHistoryRelativeCurvaturePrimeLift_sameHistory_ne_zero
    (n : ℕ) (p q : Nat.Primes) :
    historyStokesKernel PrimeHodgeHistory.relativeCurvatureWeight 1
      ((n, p), (n, q)) ≠ 0 := by
  exact historyStokesKernel_sameHistory_ne_zero
    PrimeHodgeHistory.relativeCurvatureWeight
    PrimeHodgeHistory.relativeCurvatureWeight_pos zero_lt_one n p q

theorem primeHodgeHistoryRelativeCurvaturePrimeLift_historyMarginal (n : ℕ) :
    (∑' p : Nat.Primes,
      historyStokesDiagonalWeight PrimeHodgeHistory.relativeCurvatureWeight 1 (n, p)) =
      PrimeHodgeHistory.relativeCurvatureWeight n := by
  exact tsum_historyStokesDiagonalWeight_prime
    PrimeHodgeHistory.relativeCurvatureWeight n zero_lt_one

theorem relativeCurvature_historyStokesKernel_eq_sub :
    historyStokesKernel PrimeHodgeHistory.relativeCurvatureWeight 1 =
      historyStokesKernel PrimeHodgeHistory.outgoingMetricWeight 1 -
        historyStokesKernel PrimeHodgeHistory.exitHazard 1 := by
  funext ab
  by_cases h : ab.1.1 = ab.2.1
  · simp only [historyStokesKernel, h, if_true, Pi.sub_apply]
    rw [← sub_mul]
    have hweight : (PrimeHodgeHistory.relativeCurvatureWeight ab.1.1 : ℂ) =
        (PrimeHodgeHistory.outgoingMetricWeight ab.1.1 : ℂ) -
          (PrimeHodgeHistory.exitHazard ab.1.1 : ℂ) := by
      exact_mod_cast
        (PrimeHodgeHistory.outgoing_sub_incoming_eq_relativeCurvatureWeight ab.1.1).symm
    rw [← h]
    rw [hweight]
  · simp [historyStokesKernel, h]

theorem primeHodgeHistoryRelativeCurvaturePrimeLift_eq_metric_sub :
    primeHodgeHistoryRelativeCurvaturePrimeLift =
      primeHodgeHistoryOutgoingPrimeMetric - primeHodgeHistoryIncomingPrimeMetric := by
  unfold primeHodgeHistoryRelativeCurvaturePrimeLift
    primeHodgeHistoryOutgoingPrimeMetric primeHodgeHistoryIncomingPrimeMetric
    historyStokesOperator
  rw [HilbertSchmidt.toOperator_sub]
  apply HilbertSchmidt.toOperator_congr
  exact relativeCurvature_historyStokesKernel_eq_sub

theorem primeHodgeHistoryRelativeCurvaturePrimeLift_closed :
    primeHodgeHistoryOutgoingPrimeMetric.IsPositive ∧
      IsCompactOperator primeHodgeHistoryOutgoingPrimeMetric ∧
      ¬ MemSchattenClass 1 primeHodgeHistoryOutgoingPrimeMetric ∧
      primeHodgeHistoryIncomingPrimeMetric.IsPositive ∧
      IsCompactOperator primeHodgeHistoryIncomingPrimeMetric ∧
      ¬ MemSchattenClass 1 primeHodgeHistoryIncomingPrimeMetric ∧
      primeHodgeHistoryRelativeCurvaturePrimeLift =
        primeHodgeHistoryOutgoingPrimeMetric - primeHodgeHistoryIncomingPrimeMetric ∧
      primeHodgeHistoryRelativeCurvaturePrimeLift.IsPositive ∧
      MemSchattenClass 1 primeHodgeHistoryRelativeCurvaturePrimeLift ∧
      ContinuousLinearMap.opTrace primeHodgeHistoryRelativeCurvaturePrimeLift = 1 ∧
      traceNorm PrimeHodgeHistoryHilbert primeHodgeHistoryRelativeCurvaturePrimeLift = 1 ∧
      ‖primeHodgeHistoryRelativeCurvaturePrimeLift‖ ≤ 1 / 3 ∧
      (∀ n p q, historyStokesKernel PrimeHodgeHistory.relativeCurvatureWeight 1
        ((n, p), (n, q)) ≠ 0) ∧
      (∀ n, (∑' p : Nat.Primes,
        historyStokesDiagonalWeight PrimeHodgeHistory.relativeCurvatureWeight 1 (n, p)) =
          PrimeHodgeHistory.relativeCurvatureWeight n) := by
  exact ⟨primeHodgeHistoryOutgoingPrimeMetric_isPositive,
    primeHodgeHistoryOutgoingPrimeMetric_isCompactOperator,
    primeHodgeHistoryOutgoingPrimeMetric_not_memSchattenClass_one,
    primeHodgeHistoryIncomingPrimeMetric_isPositive,
    primeHodgeHistoryIncomingPrimeMetric_isCompactOperator,
    primeHodgeHistoryIncomingPrimeMetric_not_memSchattenClass_one,
    primeHodgeHistoryRelativeCurvaturePrimeLift_eq_metric_sub,
    primeHodgeHistoryRelativeCurvaturePrimeLift_isPositive,
    primeHodgeHistoryRelativeCurvaturePrimeLift_memSchattenClass_one,
    opTrace_primeHodgeHistoryRelativeCurvaturePrimeLift,
    traceNorm_primeHodgeHistoryRelativeCurvaturePrimeLift,
    norm_primeHodgeHistoryRelativeCurvaturePrimeLift_le_one_third,
    primeHodgeHistoryRelativeCurvaturePrimeLift_sameHistory_ne_zero,
    primeHodgeHistoryRelativeCurvaturePrimeLift_historyMarginal⟩

end

end RHTower
