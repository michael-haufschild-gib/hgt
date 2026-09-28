import GaloisForLFunctions.RHTower.Sieve.PrimeSetPowerCoefficients
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueLemma34
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifier

/-!
# Heath-Brown's Lemma 3.4 for truncated Dirichlet polynomials on the one-line

Matomäki–Teräväinen Lemma 3.4 (`integral_Icc_normSq_heathBrown_oneLine_le_lemma34`) takes a sparse
factor with coefficients of modulus `≤ 1` supported on `[M, T]` and a dense factor with real
coefficients on one dyadic block `(N, 2N]`.  Here both factors are truncated Dirichlet polynomials
`perronPoly c K 1 t = ∑_{n ≤ K} c_n n^{-1-it}`, and the dense coefficients may be complex and supported
on `(N, N·2^R]`.  Splitting into real and imaginary parts and into `R` dyadic blocks (Cauchy–Schwarz)
costs the factor `4R²`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The positive elements of a finite set of naturals, as a finite set of positive naturals. -/
def pnatFinset (s : Finset ℕ) : Finset PNat :=
  s.preimage (fun n : PNat => (n : ℕ)) (PNat.coe_injective.injOn)

theorem sum_pnatFinset {β : Type*} [AddCommMonoid β] (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n)
    (F : PNat → β) (G : ℕ → β) (hFG : ∀ n : PNat, F n = G n) :
    ∑ n ∈ pnatFinset s, F n = ∑ n ∈ s, G n := by
  rw [pnatFinset, ← Finset.sum_preimage (fun n : PNat => (n : ℕ)) s PNat.coe_injective.injOn G
    (fun n hn hnr => absurd ⟨⟨n, hs n hn⟩, rfl⟩ hnr)]
  exact Finset.sum_congr rfl fun n _ => hFG n

theorem card_pnatFinset_le (s : Finset ℕ) : (pnatFinset s).card ≤ s.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun n : PNat => (n : ℕ)) (fun n hn => ?_)
    PNat.coe_injective.injOn
  exact Finset.mem_preimage.1 hn

/-- The one-line Dirichlet term: `n^{-1-it} = n⁻¹ · e^{-it log n}`. -/
theorem natCast_cpow_neg_one_add_eq_phase (n : PNat) (t : ℝ) :
    (((n : ℕ) : ℂ)) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) =
      (((1 / ((n : ℕ) : ℝ) : ℝ)) : ℂ) * heathBrownDirichletPhase n t := by
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  rw [heathBrownDirichletPhase, show (((n : ℕ) : ℂ)) = ((((n : ℕ) : ℝ)) : ℂ) by simp,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), ← Complex.ofReal_log hn.le]
  rw [show (Real.log ((n : ℕ) : ℝ) : ℂ) * -(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) =
      ((-Real.log ((n : ℕ) : ℝ) : ℝ) : ℂ) + (-((t * Real.log ((n : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) by
    push_cast; ring]
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hn, one_div]

/-- A truncated one-line Dirichlet polynomial is Heath-Brown's sparse factor on its support. -/
theorem perronPoly_one_eq_heathBrownSparse (e : ℕ → ℂ) (K : ℕ) (t : ℝ) :
    perronPoly e K 1 t =
      heathBrownSparseOneLineFactor (pnatFinset ((Finset.Icc 1 K).filter fun m => e m ≠ 0)) e t := by
  classical
  rw [heathBrownSparseOneLineFactor, perronPoly]
  rw [sum_pnatFinset _ (fun n hn => (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1)
    (fun m : PNat => e (m : ℕ) * ((((1 / ((m : ℕ) : ℝ)) : ℝ)) : ℂ) * heathBrownDirichletPhase m t)
    (fun m => e m * (m : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)))
    (fun m => by
      rw [natCast_cpow_neg_one_add_eq_phase]
      ring)]
  exact (Finset.sum_filter_of_ne fun m _ hm => left_ne_zero_of_mul hm).symm

theorem heathBrownDenseCoefficientMax_le {B : Finset PNat} {a : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ n ∈ B, |a (n : ℕ)| ≤ K) : heathBrownDenseCoefficientMax B a ≤ K := by
  classical
  rw [heathBrownDenseCoefficientMax]
  split_ifs with hB
  · exact Finset.sup'_le hB _ ha
  · exact hK

/-- A block of a one-line Dirichlet polynomial with complex coefficients is the sum of the real and
`i` times the imaginary Heath-Brown dense factors. -/
theorem sum_cpow_eq_heathBrownDense_re_add_im (c : ℕ → ℂ) (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n)
    (t : ℝ) :
    ∑ n ∈ s, c n * (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) =
      heathBrownDenseOneLineFactor (pnatFinset s) (fun n => (c n).re) t +
        Complex.I * heathBrownDenseOneLineFactor (pnatFinset s) (fun n => (c n).im) t := by
  have hterm : ∀ (a : ℕ → ℝ) (n : PNat),
      (((a (n : ℕ) / ((n : ℕ) : ℝ) : ℝ)) : ℂ) * heathBrownDirichletPhase n t =
        (a n : ℂ) * (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) := by
    intro a n
    rw [natCast_cpow_neg_one_add_eq_phase, div_eq_mul_one_div, Complex.ofReal_mul]
    ring
  rw [heathBrownDenseOneLineFactor, heathBrownDenseOneLineFactor,
    sum_pnatFinset s hs _
      (fun n => (((c n).re : ℝ) : ℂ) * (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)))
      (hterm fun n => (c n).re),
    sum_pnatFinset s hs _
      (fun n => (((c n).im : ℝ) : ℂ) * (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)))
      (hterm fun n => (c n).im), Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  conv_lhs => rw [← Complex.re_add_im (c n)]
  ring

/-- Pointwise splitting of a sparse factor times a sum of `R` complex blocks. -/
theorem norm_mul_sum_add_I_mul_sq_le (S : ℂ) (u v : ℕ → ℂ) (R : ℕ) :
    ‖S * ∑ r ∈ Finset.range R, (u r + Complex.I * v r)‖ ^ 2 ≤
      2 * R * ∑ r ∈ Finset.range R, (‖S * u r‖ ^ 2 + ‖S * v r‖ ^ 2) := by
  have h1 : ‖S * ∑ r ∈ Finset.range R, (u r + Complex.I * v r)‖ ≤
      ∑ r ∈ Finset.range R, (‖S * u r‖ + ‖S * v r‖) := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    rw [mul_add]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [show S * (Complex.I * v r) = Complex.I * (S * v r) by ring, norm_mul Complex.I,
      Complex.norm_I, one_mul]
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range R)
    (f := fun r => ‖S * u r‖ + ‖S * v r‖)
  rw [Finset.card_range] at h2
  have h3 : ∀ r ∈ Finset.range R, (‖S * u r‖ + ‖S * v r‖) ^ 2 ≤
      2 * (‖S * u r‖ ^ 2 + ‖S * v r‖ ^ 2) := fun r _ => by
    nlinarith [sq_nonneg (‖S * u r‖ - ‖S * v r‖)]
  calc ‖S * ∑ r ∈ Finset.range R, (u r + Complex.I * v r)‖ ^ 2
      ≤ (∑ r ∈ Finset.range R, (‖S * u r‖ + ‖S * v r‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ R * ∑ r ∈ Finset.range R, (‖S * u r‖ + ‖S * v r‖) ^ 2 := h2
    _ ≤ R * ∑ r ∈ Finset.range R, 2 * (‖S * u r‖ ^ 2 + ‖S * v r‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum h3) (Nat.cast_nonneg _)
    _ = 2 * R * ∑ r ∈ Finset.range R, (‖S * u r‖ ^ 2 + ‖S * v r‖ ^ 2) := by
        rw [← Finset.mul_sum]; ring

/-- The dense Dirichlet polynomial, supported in `(N, N·2^R]`, as a sum of `R` dyadic blocks. -/
theorem perronPoly_one_eq_sum_dyadic_blocks (c : ℕ → ℂ) (K N R : ℕ)
    (hc : ∀ n, c n ≠ 0 → n ≤ K ∧ N < n ∧ n ≤ N * 2 ^ R) (t : ℝ) :
    perronPoly c K 1 t =
      ∑ r ∈ Finset.range R,
        (heathBrownDenseOneLineFactor (pnatFinset (Finset.Ioc (N * 2 ^ r) (N * 2 ^ (r + 1))))
            (fun n => (c n).re) t +
          Complex.I * heathBrownDenseOneLineFactor
            (pnatFinset (Finset.Ioc (N * 2 ^ r) (N * 2 ^ (r + 1)))) (fun n => (c n).im) t) := by
  classical
  set f : ℕ → ℂ := fun n => c n * (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) with hf
  have hf0 : ∀ n, f n ≠ 0 → n ≤ K ∧ N < n ∧ n ≤ N * 2 ^ R := fun n hn =>
    hc n (left_ne_zero_of_mul hn)
  have hsum : ∑ n ∈ Finset.Icc 1 K, f n = ∑ n ∈ Finset.Ioc N (N * 2 ^ R), f n := by
    have e1 : ∑ n ∈ Finset.Icc 1 K, f n = ∑ n ∈ Finset.Icc 1 K ∪ Finset.Ioc N (N * 2 ^ R), f n :=
      Finset.sum_subset Finset.subset_union_left fun n _ hn => by
        by_contra hne
        obtain ⟨h1, h2, _⟩ := hf0 n hne
        exact hn (Finset.mem_Icc.2 ⟨by omega, h1⟩)
    have e2 : ∑ n ∈ Finset.Ioc N (N * 2 ^ R), f n =
        ∑ n ∈ Finset.Icc 1 K ∪ Finset.Ioc N (N * 2 ^ R), f n :=
      Finset.sum_subset Finset.subset_union_right fun n _ hn => by
        by_contra hne
        obtain ⟨_, h2, h3⟩ := hf0 n hne
        exact hn (Finset.mem_Ioc.2 ⟨h2, h3⟩)
    rw [e1, e2]
  change ∑ n ∈ Finset.Icc 1 K, f n = _
  rw [hsum, mtSum_Ioc_dyadic]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact sum_cpow_eq_heathBrownDense_re_add_im c _
    (fun n hn => by have := (Finset.mem_Ioc.1 hn).1; omega) t

theorem heathBrownLemma34Coefficient_nonneg (eta : ℝ) :
    0 ≤ heathBrownLemma34Coefficient eta := by
  have hC : 0 ≤ heathBrownTheoremFourCoefficient eta := by
    dsimp [heathBrownTheoremFourCoefficient,
      heathBrownTheoremFourUniversalCoefficient, heathBrownMeanSquareCoefficient]
    positivity
  unfold heathBrownLemma34Coefficient heathBrownLemma34PositiveCoefficient
  positivity

/-- The bracket of Lemma 3.4 at sparse cardinality `A`, dense scale `N`, height `T`, and the
`η`-loss taken at scale `L`. -/
def heathBrownLemma34Bracket (A M N L T eta : ℝ) : ℝ :=
  (A / M) ^ 2 + (L * T) ^ eta * (A * T / (M ^ 2 * N) + A ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) / (M ^ 2 * N))

theorem heathBrownLemma34Bracket_mono {A A' M N N' L L' T eta : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A')
    (hM : 0 < M) (hN : 0 < N) (hNN : N ≤ N') (hL : 0 ≤ L) (hLL : L ≤ L') (hT : 0 ≤ T)
    (heta : 0 ≤ eta) :
    heathBrownLemma34Bracket A M N' L T eta ≤ heathBrownLemma34Bracket A' M N L' T eta := by
  unfold heathBrownLemma34Bracket
  have hA' : 0 ≤ A' := hA.trans hAA
  have h7 : A ^ (7 / 4 : ℝ) ≤ A' ^ (7 / 4 : ℝ) := Real.rpow_le_rpow hA hAA (by norm_num)
  have hN' : 0 < N' := hN.trans_le hNN
  have hLT : 0 ≤ (L' * T) ^ eta := Real.rpow_nonneg (mul_nonneg (hL.trans hLL) hT) _
  gcongr

/-- One dyadic real block against the sparse factor, with the block bounds relaxed to the whole
range `(N, N·2^R]`. -/
theorem integral_normSq_sparse_block_le {A : Finset PNat} {e : ℕ → ℂ} {M T : ℝ} (hM : 1 ≤ M)
    (hT : 0 < T) (hMT : M ≤ T) (hAM : ∀ m ∈ A, M ≤ ((m : ℕ) : ℝ)) (he1 : ∀ m, ‖e m‖ ≤ 1)
    (hAT : ∀ m ∈ A, ((m : ℕ) : ℝ) ≤ T) {Acard : ℝ} (hAcard : (A.card : ℝ) ≤ Acard)
    {N R r : ℕ} (hN : 2 ≤ N) (hr : r < R) (a : ℕ → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (ha : ∀ n, |a n| ≤ B) {eta : ℝ} (heta : 0 < eta) :
    ∫ t in Set.Icc (-T) T, ‖heathBrownSparseOneLineFactor A e t *
        heathBrownDenseOneLineFactor (pnatFinset (Finset.Ioc (N * 2 ^ r) (N * 2 ^ (r + 1)))) a t‖ ^ 2
      ≤ heathBrownLemma34Coefficient eta * B ^ 2 *
        heathBrownLemma34Bracket Acard M N ((N * 2 ^ R : ℕ) : ℝ) T eta := by
  set D := pnatFinset (Finset.Ioc (N * 2 ^ r) (N * 2 ^ (r + 1))) with hD
  have hNr : 2 ≤ N * 2 ^ r := le_trans hN (Nat.le_mul_of_pos_right N (by positivity))
  have hmemD : ∀ n ∈ D, N * 2 ^ r < (n : ℕ) ∧ (n : ℕ) ≤ 2 * (N * 2 ^ r) := by
    intro n hn
    have := Finset.mem_Ioc.1 (Finset.mem_preimage.1 hn)
    exact ⟨this.1, by rw [pow_succ] at this; linarith [this.2]⟩
  have hmain := integral_Icc_normSq_heathBrown_oneLine_le_lemma34 A D e a hM hAM
    (fun m _ => he1 m) ⟨T, hT⟩ hMT hAT hNr (fun n hn => (hmemD n hn).1)
    (fun n hn => (hmemD n hn).2) heta
  refine hmain.trans ?_
  have hC := heathBrownLemma34Coefficient_nonneg eta
  have hK := heathBrownDenseCoefficientMax_le hB0 (B := D) (fun n _ => ha n)
  have hK0 := heathBrownDenseCoefficientMax_nonneg D a
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNr_ge : (N : ℝ) ≤ ((N * 2 ^ r : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_right N (by positivity)
  have hNr_le : ((N * 2 ^ r : ℕ) : ℝ) ≤ ((N * 2 ^ R : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left N (Nat.pow_le_pow_right (by norm_num) hr.le)
  have hbr := heathBrownLemma34Bracket_mono (T := T) (eta := eta) (Nat.cast_nonneg A.card) hAcard
    (by linarith : (0 : ℝ) < M) hNpos hNr_ge (Nat.cast_nonneg _) hNr_le hT.le heta.le
  have hKB : heathBrownDenseCoefficientMax D a ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hK0 hK 2
  change heathBrownLemma34Coefficient eta * heathBrownDenseCoefficientMax D a ^ 2 *
      heathBrownLemma34Bracket (A.card : ℝ) M ((N * 2 ^ r : ℕ) : ℝ) ((N * 2 ^ r : ℕ) : ℝ) T eta
    ≤ _
  have hbr0 : 0 ≤ heathBrownLemma34Bracket (A.card : ℝ) M ((N * 2 ^ r : ℕ) : ℝ)
      ((N * 2 ^ r : ℕ) : ℝ) T eta := by
    unfold heathBrownLemma34Bracket; positivity
  calc heathBrownLemma34Coefficient eta * heathBrownDenseCoefficientMax D a ^ 2 *
        heathBrownLemma34Bracket (A.card : ℝ) M ((N * 2 ^ r : ℕ) : ℝ) ((N * 2 ^ r : ℕ) : ℝ) T eta
      ≤ heathBrownLemma34Coefficient eta * B ^ 2 *
        heathBrownLemma34Bracket (A.card : ℝ) M ((N * 2 ^ r : ℕ) : ℝ) ((N * 2 ^ r : ℕ) : ℝ) T eta := by
        gcongr
    _ ≤ _ := by gcongr

/-- **Lemma 3.4 for truncated one-line Dirichlet polynomials.**  Sparse coefficients `|e_m| ≤ 1`
supported on `[M, T]`; dense complex coefficients `|c_n| ≤ B` supported on `(N, N·2^R]`. -/
theorem integral_normSq_perronPoly_mul_le_lemma34 (e c : ℕ → ℂ) (K₁ K₂ : ℕ) {M T : ℝ}
    (hM : 1 ≤ M) (hT : 0 < T) (hMT : M ≤ T)
    (he : ∀ m, e m ≠ 0 → M ≤ m ∧ (m : ℝ) ≤ T) (he1 : ∀ m, ‖e m‖ ≤ 1)
    {N R : ℕ} (hN : 2 ≤ N) (hc : ∀ n, c n ≠ 0 → n ≤ K₂ ∧ N < n ∧ n ≤ N * 2 ^ R)
    {B : ℝ} (hB : ∀ n, ‖c n‖ ≤ B) {eta : ℝ} (heta : 0 < eta) :
    ∫ t in Set.Icc (-T) T, ‖perronPoly e K₁ 1 t * perronPoly c K₂ 1 t‖ ^ 2 ≤
      4 * R ^ 2 * heathBrownLemma34Coefficient eta * B ^ 2 *
        heathBrownLemma34Bracket (((Finset.Icc 1 K₁).filter fun m => e m ≠ 0).card : ℝ) M N
          ((N * 2 ^ R : ℕ) : ℝ) T eta := by
  classical
  set Af := (Finset.Icc 1 K₁).filter fun m => e m ≠ 0 with hAf
  set A := pnatFinset Af with hA
  set Q : ℝ := heathBrownLemma34Bracket (Af.card : ℝ) M N ((N * 2 ^ R : ℕ) : ℝ) T eta with hQ
  set C := heathBrownLemma34Coefficient eta with hCdef
  set S : ℝ → ℂ := heathBrownSparseOneLineFactor A e with hS
  set Dre : ℕ → ℝ → ℂ := fun r => heathBrownDenseOneLineFactor
    (pnatFinset (Finset.Ioc (N * 2 ^ r) (N * 2 ^ (r + 1)))) (fun n => (c n).re) with hDre
  set Dim : ℕ → ℝ → ℂ := fun r => heathBrownDenseOneLineFactor
    (pnatFinset (Finset.Ioc (N * 2 ^ r) (N * 2 ^ (r + 1)))) (fun n => (c n).im) with hDim
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hAM : ∀ m ∈ A, M ≤ ((m : ℕ) : ℝ) := fun m hm =>
    (he m (Finset.mem_filter.1 (Finset.mem_preimage.1 hm)).2).1
  have hAT : ∀ m ∈ A, ((m : ℕ) : ℝ) ≤ T := fun m hm =>
    (he m (Finset.mem_filter.1 (Finset.mem_preimage.1 hm)).2).2
  have hAcard : (A.card : ℝ) ≤ Af.card := by exact_mod_cast card_pnatFinset_le Af
  have hpt : ∀ t, ‖perronPoly e K₁ 1 t * perronPoly c K₂ 1 t‖ ^ 2 ≤
      2 * R * ∑ r ∈ Finset.range R, (‖S t * Dre r t‖ ^ 2 + ‖S t * Dim r t‖ ^ 2) := by
    intro t
    rw [perronPoly_one_eq_heathBrownSparse, perronPoly_one_eq_sum_dyadic_blocks c K₂ N R hc t]
    exact norm_mul_sum_add_I_mul_sq_le _ _ _ R
  have hcontS : Continuous S := continuous_heathBrownSparseOneLineFactor A e
  have hcont : ∀ (D : ℝ → ℂ), Continuous D → Continuous fun t => ‖S t * D t‖ ^ 2 :=
    fun D hD => ((hcontS.mul hD).norm).pow 2
  have hcDre : ∀ r, Continuous (Dre r) := fun r => continuous_heathBrownDenseOneLineFactor _ _
  have hcDim : ∀ r, Continuous (Dim r) := fun r => continuous_heathBrownDenseOneLineFactor _ _
  have hint : ∀ (D : ℝ → ℂ), Continuous D →
      IntegrableOn (fun t => ‖S t * D t‖ ^ 2) (Set.Icc (-T) T) :=
    fun D hD => (hcont D hD).integrableOn_Icc
  have hLint : IntegrableOn (fun t => ‖perronPoly e K₁ 1 t * perronPoly c K₂ 1 t‖ ^ 2)
      (Set.Icc (-T) T) :=
    (((continuous_perronPoly e K₁ 1).mul (continuous_perronPoly c K₂ 1)).norm.pow 2).integrableOn_Icc
  have hRint : IntegrableOn
      (fun t => 2 * R * ∑ r ∈ Finset.range R, (‖S t * Dre r t‖ ^ 2 + ‖S t * Dim r t‖ ^ 2))
      (Set.Icc (-T) T) := by
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ fun r _ => ?_
    exact (hint _ (hcDre r)).add (hint _ (hcDim r))
  have hblock : ∀ r ∈ Finset.range R,
      (∫ t in Set.Icc (-T) T, ‖S t * Dre r t‖ ^ 2) + (∫ t in Set.Icc (-T) T, ‖S t * Dim r t‖ ^ 2)
        ≤ 2 * (C * B ^ 2 * Q) := by
    intro r hr
    have hr' : r < R := Finset.mem_range.1 hr
    have h1 := integral_normSq_sparse_block_le hM hT hMT hAM he1 hAT hAcard hN hr'
      (fun n => (c n).re) hB0 (fun n => (Complex.abs_re_le_norm (c n)).trans (hB n)) heta
    have h2 := integral_normSq_sparse_block_le hM hT hMT hAM he1 hAT hAcard hN hr'
      (fun n => (c n).im) hB0 (fun n => (Complex.abs_im_le_norm (c n)).trans (hB n)) heta
    change (∫ t in Set.Icc (-T) T, ‖S t * Dre r t‖ ^ 2) ≤ C * B ^ 2 * Q at h1
    change (∫ t in Set.Icc (-T) T, ‖S t * Dim r t‖ ^ 2) ≤ C * B ^ 2 * Q at h2
    linarith
  calc ∫ t in Set.Icc (-T) T, ‖perronPoly e K₁ 1 t * perronPoly c K₂ 1 t‖ ^ 2
      ≤ ∫ t in Set.Icc (-T) T,
          2 * R * ∑ r ∈ Finset.range R, (‖S t * Dre r t‖ ^ 2 + ‖S t * Dim r t‖ ^ 2) :=
        setIntegral_mono hLint hRint hpt
    _ = 2 * R * ∑ r ∈ Finset.range R, ((∫ t in Set.Icc (-T) T, ‖S t * Dre r t‖ ^ 2) +
          (∫ t in Set.Icc (-T) T, ‖S t * Dim r t‖ ^ 2)) := by
        have hsumint : ∀ r ∈ Finset.range R, Integrable
            (fun t => ‖S t * Dre r t‖ ^ 2 + ‖S t * Dim r t‖ ^ 2) (volume.restrict (Set.Icc (-T) T)) :=
          fun r _ => (hint _ (hcDre r)).add (hint _ (hcDim r))
        rw [integral_const_mul, integral_finsetSum _ hsumint]
        refine congrArg _ (Finset.sum_congr rfl fun r _ => ?_)
        exact integral_add (hint _ (hcDre r)) (hint _ (hcDim r))
    _ ≤ 2 * R * ∑ _r ∈ Finset.range R, 2 * (C * B ^ 2 * Q) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hblock) (by positivity)
    _ = 4 * R ^ 2 * C * B ^ 2 * Q := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end

end RHTower.Sieve
