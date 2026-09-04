import GaloisForLFunctions.RHTower.Sieve.MaynardComplementaryMontgomeryFiniteSet
import GaloisForLFunctions.RHTower.Sieve.ProdIdxFibreDivisorBound
import GaloisForLFunctions.RHTower.Sieve.DirichletFirstMomentShift
import GaloisForLFunctions.RHTower.Sieve.HalaszMontgomeryLogPolyBlock
import GaloisForLFunctions.RHTower.Sieve.HuxleyRangeLargeValues
import GaloisForLFunctions.RHTower.Sieve.DirichletConvolutionDivisorReindex

/-!
# Same-frequency Heath--Brown/cofactor Montgomery estimate

A literal grouped Heath--Brown product and an arbitrary second Dirichlet polynomial multiply to
the exact finite Dirichlet convolution.  This retains the final Ramaré cofactor in Menon's
Case-II mean-square argument instead of discarding it by a pointwise bound.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Halász--Montgomery for a dyadic block on a finite subset of an ambient separated sequence,
at an arbitrary vertical line. -/
theorem halaszMontgomery_blockPoly_finset_sigma
    (N : ℕ) (hN : 1 ≤ N) (c : ℕ → ℂ) (sigma : ℝ)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta U T : ℝ}
    (hdelta : 0 < delta) (hU : 0 < U) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1) :
    ∑ r ∈ S, ‖blockPoly N c sigma (lam r)‖ ^ 2 ≤
      ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log S.card)
          + (S.card : ℝ) *
            (1 + 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U))) *
        ‖blockCoeff N c sigma‖ ^ 2 := by
  classical
  by_cases hS : S.Nonempty
  · let ext : ℕ → ℝ := finsetSeparatedExtension S hS lam delta
    have hextgap : ∀ i, ext i + delta ≤ ext (i + 1) :=
      finsetSeparatedExtension_gap S hS lam hdelta hgap
    have hextdiam : ∀ r ∈ Finset.range S.card, ∀ s ∈ Finset.range S.card,
        |ext s - ext r| ≤ T := by
      intro r hr s hs
      have hrlt : r < S.card := Finset.mem_range.1 hr
      have hslt : s < S.card := Finset.mem_range.1 hs
      have hrmem : S.orderEmbOfFin rfl ⟨r, hrlt⟩ ∈ S := Finset.orderEmbOfFin_mem S rfl _
      have hsmem : S.orderEmbOfFin rfl ⟨s, hslt⟩ ∈ S := Finset.orderEmbOfFin_mem S rfl _
      have hrband := hband _ hrmem
      have hsband := hband _ hsmem
      rw [show ext r = lam (S.orderEmbOfFin rfl ⟨r, hrlt⟩) by
          exact finsetSeparatedExtension_eq_of_lt S hS lam delta hrlt,
        show ext s = lam (S.orderEmbOfFin rfl ⟨s, hslt⟩) by
          exact finsetSeparatedExtension_eq_of_lt S hS lam delta hslt]
      rw [abs_le]
      constructor <;> linarith
    have hbase := halaszMontgomery_dyadic_explicit (K := S.card) hN
      (blockCoeff N c sigma) hdelta hU hT hextgap hextdiam hnear hlamT
    rw [sum_finset_eq_sum_extension S hS lam delta
      (fun t => ‖blockPoly N c sigma t‖ ^ 2)]
    simpa only [inner_dyadicDirRow_blockCoeff] using hbase
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp
    positivity

/-- Sparse Halász--Montgomery mean square on a finite multiplicative range.  The range is split
into its exact `J` dyadic pieces, and no ambient-height mean-value term is introduced. -/
theorem sum_normSq_rangeTerm_finset_le_halaszMontgomery
    (A J : ℕ) (hA : 1 ≤ A) (c : ℕ → ℂ) (sigma : ℝ)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta T : ℝ} (U : ℕ → ℝ)
    (hdelta : 0 < delta) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T)
    (hU : ∀ j ∈ Finset.range J, 0 < U j)
    (hnear : ∀ j ∈ Finset.range J,
      3 * U j ≤ 4 * Real.pi * ((A * 2 ^ j : ℕ) : ℝ))
    (hlamT : ∀ j ∈ Finset.range J, logDyadicLambda (A * 2 ^ j) T ≤ 1) :
    ∑ r ∈ S,
        ‖∑ n ∈ Finset.Ico A (A * 2 ^ J), rangeTerm c sigma (lam r) n‖ ^ 2 ≤
      (J : ℝ) * ∑ j ∈ Finset.range J,
        (((A * 2 ^ j : ℕ) : ℝ) +
            (12 * Real.pi * ((A * 2 ^ j : ℕ) : ℝ) / delta) *
              (1 + Real.log S.card) +
            (S.card : ℝ) *
              (1 + 214 * Real.sqrt T +
                1536 * (((A * 2 ^ j : ℕ) : ℝ) / Real.sqrt (U j)))) *
          ‖blockCoeff (A * 2 ^ j) c sigma‖ ^ 2 := by
  classical
  have hAj : ∀ j : ℕ, 1 ≤ A * 2 ^ j := by
    intro j
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hpoint : ∀ r : ℕ,
      ‖∑ n ∈ Finset.Ico A (A * 2 ^ J), rangeTerm c sigma (lam r) n‖ ^ 2 ≤
        (J : ℝ) * ∑ j ∈ Finset.range J,
          ‖blockPoly (A * 2 ^ j) c sigma (lam r)‖ ^ 2 := by
    intro r
    have htri :
        ‖∑ j ∈ Finset.range J, blockPoly (A * 2 ^ j) c sigma (lam r)‖ ≤
          ∑ j ∈ Finset.range J, ‖blockPoly (A * 2 ^ j) c sigma (lam r)‖ :=
      norm_sum_le _ _
    have hcs :
        (∑ j ∈ Finset.range J, ‖blockPoly (A * 2 ^ j) c sigma (lam r)‖) ^ 2 ≤
          (((Finset.range J).card : ℕ) : ℝ) *
            ∑ j ∈ Finset.range J, ‖blockPoly (A * 2 ^ j) c sigma (lam r)‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    rw [Finset.card_range] at hcs
    rw [sum_blockPoly_eq_range A c sigma (lam r) J] at htri
    have hnorm0 : 0 ≤
        ‖∑ n ∈ Finset.Ico A (A * 2 ^ J), rangeTerm c sigma (lam r) n‖ :=
      norm_nonneg _
    nlinarith
  calc
    ∑ r ∈ S,
        ‖∑ n ∈ Finset.Ico A (A * 2 ^ J), rangeTerm c sigma (lam r) n‖ ^ 2
        ≤ ∑ r ∈ S, (J : ℝ) * ∑ j ∈ Finset.range J,
            ‖blockPoly (A * 2 ^ j) c sigma (lam r)‖ ^ 2 :=
      Finset.sum_le_sum fun r _ => hpoint r
    _ = (J : ℝ) * ∑ j ∈ Finset.range J,
          ∑ r ∈ S, ‖blockPoly (A * 2 ^ j) c sigma (lam r)‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
    _ ≤ (J : ℝ) * ∑ j ∈ Finset.range J,
        (((A * 2 ^ j : ℕ) : ℝ) +
            (12 * Real.pi * ((A * 2 ^ j : ℕ) : ℝ) / delta) *
              (1 + Real.log S.card) +
            (S.card : ℝ) *
              (1 + 214 * Real.sqrt T +
                1536 * (((A * 2 ^ j : ℕ) : ℝ) / Real.sqrt (U j)))) *
          ‖blockCoeff (A * 2 ^ j) c sigma‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (by positivity)
      exact halaszMontgomery_blockPoly_finset_sigma (A * 2 ^ j) (hAj j) c sigma
        hdelta (hU j hj) hT hgap hband (hnear j hj) (hlamT j hj)

/-- A finite Dirichlet polynomial is its positive-natural `rangeTerm` sum at reflected
frequency. -/
theorem sum_rangeTerm_finCoeffNat_zero_eq_dirPoly_neg
    (N : ℕ) (a : Fin N → ℂ) (t : ℝ) :
    ∑ n ∈ Finset.Ico 1 (N + 1), rangeTerm (finCoeffNat N a) 0 t n =
      dirPoly N a (-t) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : N + 1 - 1 = N := by omega
  rw [hlen, ← Fin.sum_univ_eq_sum_range
    (fun j : ℕ => rangeTerm (finCoeffNat N a) 0 t (1 + j)) N]
  rw [dirPoly]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Nat.add_comm 1 (j : ℕ), finCoeffNat_succ, rangeTerm, neg_zero,
    Real.rpow_zero, Complex.ofReal_one, mul_one]
  congr 2
  push_cast
  ring

/-- Every dyadic block of a positive-natural finite coefficient vector has no more energy than
the complete vector. -/
theorem norm_blockCoeff_finCoeffNat_zero_sq_le
    (N : ℕ) (a : Fin N → ℂ) (D : ℕ) :
    ‖blockCoeff D (finCoeffNat N a) 0‖ ^ 2 ≤
      ∑ m : Fin N, ‖a m‖ ^ 2 := by
  rw [norm_blockCoeff_sq]
  simp only [neg_zero, Real.rpow_zero, one_pow, mul_one]
  let B := Finset.Ico D (2 * D)
  let F := Finset.Ico 1 (N + 1)
  have hrestrict :
      ∑ n ∈ B, ‖finCoeffNat N a n‖ ^ 2 =
        ∑ n ∈ B ∩ F, ‖finCoeffNat N a n‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.inter_subset_left)
    intro n hnB hnnot
    have hnF : n ∉ F := by
      intro hnF
      exact hnnot (Finset.mem_inter.2 ⟨hnB, hnF⟩)
    rw [finCoeffNat, dif_neg]
    · simp
    · intro hn
      apply hnF
      exact Finset.mem_Ico.2 ⟨hn.1, by omega⟩
  rw [hrestrict]
  calc
    ∑ n ∈ B ∩ F, ‖finCoeffNat N a n‖ ^ 2 ≤
        ∑ n ∈ F, ‖finCoeffNat N a n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun _ _ _ => sq_nonneg _)
    _ = ∑ m : Fin N, ‖a m‖ ^ 2 := by
      rw [show F = Finset.Ico 1 (N + 1) by rfl, Finset.sum_Ico_eq_sum_range]
      have hlen : N + 1 - 1 = N := by omega
      rw [hlen, ← Fin.sum_univ_eq_sum_range
        (fun j : ℕ => ‖finCoeffNat N a (1 + j)‖ ^ 2) N]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Nat.add_comm, finCoeffNat_succ]

/-- Restricting a finite Dirichlet polynomial to any dyadic range containing its nonzero support
is exact. -/
theorem sum_rangeTerm_finCoeffNat_zero_eq_dirPoly_neg_of_support
    (N A J : ℕ) (a : Fin N → ℂ) (t : ℝ)
    (hcover : N < A * 2 ^ J)
    (hlower : ∀ n : ℕ, n < A → finCoeffNat N a n = 0) :
    ∑ n ∈ Finset.Ico A (A * 2 ^ J), rangeTerm (finCoeffNat N a) 0 t n =
      dirPoly N a (-t) := by
  let R := A * 2 ^ J
  let D := Finset.Ico A R
  let F := Finset.Ico 1 (N + 1)
  have hDR : D ⊆ Finset.range R := by
    intro n hn
    exact Finset.mem_range.2 (Finset.mem_Ico.1 hn).2
  have hDsum :
      ∑ n ∈ D, rangeTerm (finCoeffNat N a) 0 t n =
        ∑ n ∈ Finset.range R, rangeTerm (finCoeffNat N a) 0 t n := by
    apply Finset.sum_subset hDR
    intro n hnR hnD
    have hnA : n < A := by
      have hnR' : n < R := Finset.mem_range.1 hnR
      simpa only [D, Finset.mem_Ico, hnR', and_true, not_le] using hnD
    simp only [rangeTerm, hlower n hnA, zero_mul]
  have hFR : F ⊆ Finset.range R := by
    intro n hn
    have hnN : n ≤ N := by
      have := (Finset.mem_Ico.1 hn).2
      omega
    exact Finset.mem_range.2 (lt_of_le_of_lt hnN (by simpa only [R] using hcover))
  have hFsum :
      ∑ n ∈ F, rangeTerm (finCoeffNat N a) 0 t n =
        ∑ n ∈ Finset.range R, rangeTerm (finCoeffNat N a) 0 t n := by
    apply Finset.sum_subset hFR
    intro n _hnR hnF
    have hzero : finCoeffNat N a n = 0 := by
      rw [finCoeffNat, dif_neg]
      intro hn
      apply hnF
      exact Finset.mem_Ico.2 ⟨hn.1, by omega⟩
    simp only [rangeTerm, hzero, zero_mul]
  rw [show Finset.Ico A (A * 2 ^ J) = D by rfl, hDsum, ← hFsum,
    show F = Finset.Ico 1 (N + 1) by rfl]
  exact sum_rangeTerm_finCoeffNat_zero_eq_dirPoly_neg N a t

/-- Multiplicative lower support passes through finite Dirichlet convolution. -/
theorem finCoeffNat_dirConv_eq_zero_of_lt_mul
    (N M A B : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    (ha : ∀ i : Fin N, a i ≠ 0 → A ≤ (i : ℕ) + 1)
    (hb : ∀ j : Fin M, b j ≠ 0 → B ≤ (j : ℕ) + 1)
    {n : ℕ} (hn : n < A * B) :
    finCoeffNat (N * M) (dirConv N M a b) n = 0 := by
  classical
  rw [finCoeffNat]
  split_ifs with hindex
  · rw [dirConv]
    apply Finset.sum_eq_zero
    intro q hq
    have hprod : ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) = n := by
      have hfibre := (Finset.mem_filter.1 hq).2
      have hnpos : 1 ≤ n := hindex.1
      simpa only [Nat.sub_add_cancel hnpos] using hfibre
    by_contra hqzero
    have hqa : a q.1 ≠ 0 := fun hzero => hqzero (by rw [hzero, zero_mul])
    have hqb : b q.2 ≠ 0 := fun hzero => hqzero (by rw [hzero, mul_zero])
    have hlower : A * B ≤ ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) :=
      Nat.mul_le_mul (ha q.1 hqa) (hb q.2 hqb)
    omega
  · rfl

/-- Sparse fixed-shift Heath--Brown/cofactor mean square.  Both factors retain their genuine
multiplicative lower support, so only `J` dyadic blocks beginning at that product edge are paid.
This is the finite-set large-values estimate used in Menon's medium-factor branch. -/
theorem exists_meanSquare_heathBrown_grouped_shift_mul_dirPoly_finset_sparse
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type*} [Fintype ι] [Nonempty ι]
        (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ)
        {sigma G : ℝ}, 0 ≤ sigma →
        (∑ j : Fin (groupedDyadicUpper q),
          ‖groupedDyadicCoeffVector
            (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2 ≤ G) →
        ∀ (M B J : ℕ), 1 ≤ M → 1 ≤ B → ∀ (b : Fin M → ℂ),
          (∀ m : Fin M, b m ≠ 0 → B ≤ (m : ℕ) + 1) →
          (groupedDyadicUpper q) * M <
            (groupedDyadicLower q * B) * 2 ^ J →
          ∀ (u : ℝ) {S : Finset ℕ} {lam : ℕ → ℝ} {delta T : ℝ}
            (U : ℕ → ℝ),
          0 < delta → 0 ≤ T →
          (∀ i, lam i + delta ≤ lam (i + 1)) →
          (∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T) →
          (∀ j ∈ Finset.range J, 0 < U j) →
          (∀ j ∈ Finset.range J,
            3 * U j ≤ 4 * Real.pi *
              (((groupedDyadicLower q * B) * 2 ^ j : ℕ) : ℝ)) →
          (∀ j ∈ Finset.range J,
            logDyadicLambda ((groupedDyadicLower q * B) * 2 ^ j) T ≤ 1) →
          ∑ r ∈ S,
              ‖(∏ i, LSeries
                (complexCoeff (arithmeticDyadicBlock
                  (heathBrownFactorBase L X (kind i)) (q i)))
                  ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I)) *
                dirPoly M b (-lam r)‖ ^ 2 ≤
            (J : ℝ) *
              (∑ j ∈ Finset.range J,
                ((((groupedDyadicLower q * B) * 2 ^ j : ℕ) : ℝ) +
                    (12 * Real.pi *
                        (((groupedDyadicLower q * B) * 2 ^ j : ℕ) : ℝ) / delta) *
                      (1 + Real.log S.card) +
                    (S.card : ℝ) *
                      (1 + 214 * Real.sqrt T +
                        1536 *
                          ((((groupedDyadicLower q * B) * 2 ^ j : ℕ) : ℝ) /
                            Real.sqrt (U j))))) *
              (C * ((((groupedDyadicUpper q) * M : ℕ) : ℝ)) ^ epsilon *
                ((((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 * G) *
                  ∑ m : Fin M, ‖b m‖ ^ 2)) := by
  obtain ⟨C, hC, hconv⟩ := exists_sum_norm_sq_dirConv_le_rpow hepsilon
  refine ⟨C, hC, ?_⟩
  intro ι instFintype instNonempty L X kind q sigma G hsigma henergy M B J hM hB b
    hb hcover u S lam delta T U hdelta hT hgap hband hU hnear hlamT
  let F : ι → ArithmeticFunction ℝ := fun i => heathBrownFactorBase L X (kind i)
  let N : ℕ := groupedDyadicUpper q
  let A : ℕ := groupedDyadicLower q * B
  let a0 : Fin N → ℂ :=
    sigmaWeightedCoeff N (groupedDyadicCoeffVector F q) sigma
  let a : Fin N → ℂ := fun i => a0 i *
    Complex.exp (((-u * Real.log (((i : ℕ) : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
  let c : Fin (N * M) → ℂ := dirConv N M a b
  let cn : ℕ → ℂ := finCoeffNat (N * M) c
  have hA : 1 ≤ A := by
    exact Nat.mul_le_mul (one_le_groupedDyadicLower q) hB
  have haSupport : ∀ i : Fin N, a i ≠ 0 → groupedDyadicLower q ≤ (i : ℕ) + 1 := by
    intro i hi
    have ha0 : a0 i ≠ 0 := fun hzero => hi (by simp only [a, hzero, zero_mul])
    have hgroup : groupedDyadicCoeffVector F q i ≠ 0 := by
      intro hzero
      exact ha0 (by simp only [a0, sigmaWeightedCoeff, hzero, zero_mul])
    exact (groupedDyadicCoeffVector_support_fixedWidth F q i hgroup).1
  have hcLower : ∀ n : ℕ, n < A → cn n = 0 := by
    intro n hn
    exact finCoeffNat_dirConv_eq_zero_of_lt_mul N M (groupedDyadicLower q) B a b
      haSupport hb (by simpa only [A] using hn)
  have hpoint : ∀ r : ℕ,
      ‖(∏ i, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i)))
            ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I)) *
          dirPoly M b (-lam r)‖ =
        ‖∑ n ∈ Finset.Ico A (A * 2 ^ J), rangeTerm cn 0 (lam r) n‖ := by
    intro r
    have hgroup0 :
        (∏ i, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i)))
            ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I)) =
          dirPoly N a0 (-(u + lam r)) := by
      symm
      simpa only [F, N, a0] using
        dirPoly_groupedDyadicCoeffVector_eq_product F q sigma (u + lam r)
    have hshift : dirPoly N a0 (-(u + lam r)) = dirPoly N a (-lam r) := by
      have ht := dirPoly_translate N a0 (-u) (-lam r)
      rw [show -u + -lam r = -(u + lam r) by ring] at ht
      simpa only [a] using ht
    rw [hgroup0, hshift, dirPoly_mul_eq_dirPoly]
    rw [sum_rangeTerm_finCoeffNat_zero_eq_dirPoly_neg_of_support
      (N * M) A J c (lam r) (by simpa only [N, A] using hcover) hcLower]
  have hrange := sum_normSq_rangeTerm_finset_le_halaszMontgomery A J hA cn 0 U
    hdelta hT hgap hband hU hnear hlamT
  have hsum :
      (∑ r ∈ S,
          ‖(∏ i, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (kind i)) (q i)))
              ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I)) *
            dirPoly M b (-lam r)‖ ^ 2) =
        ∑ r ∈ S,
          ‖∑ n ∈ Finset.Ico A (A * 2 ^ J), rangeTerm cn 0 (lam r) n‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro r _hr
    rw [hpoint r]
  rw [hsum]
  let E : ℝ := C * (((N * M : ℕ) : ℝ)) ^ epsilon *
    ((((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 * G) *
      ∑ m : Fin M, ‖b m‖ ^ 2)
  have haeq : ∑ j : Fin N, ‖a j‖ ^ 2 = ∑ j : Fin N, ‖a0 j‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [show ‖a j‖ = ‖a0 j‖ by
      simpa only [a] using norm_dirPoly_twist_coeff N a0 (-u) j]
  have haenergy : ∑ j : Fin N, ‖a j‖ ^ 2 ≤
      ((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 * G := by
    rw [haeq]
    simpa only [F, N, a0] using
      sum_normSq_sigmaWeighted_grouped_le F q hsigma henergy
  have hcenergy : ∑ n : Fin (N * M), ‖c n‖ ^ 2 ≤ E := by
    have hraw := hconv N M a b
    exact hraw.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right haenergy
        (Finset.sum_nonneg fun m _ => sq_nonneg ‖b m‖))
      (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)))
  have hlogCard : 0 ≤ Real.log (S.card : ℝ) := by
    by_cases hcard : S.card = 0
    · simp [hcard]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hcard)
  have hfactor0 : ∀ j : ℕ,
      0 ≤ (((A * 2 ^ j : ℕ) : ℝ) +
          (12 * Real.pi * ((A * 2 ^ j : ℕ) : ℝ) / delta) *
            (1 + Real.log S.card) +
          (S.card : ℝ) *
            (1 + 214 * Real.sqrt T +
              1536 * (((A * 2 ^ j : ℕ) : ℝ) / Real.sqrt (U j)))) := by
    intro j
    have hlog1 : 0 ≤ 1 + Real.log (S.card : ℝ) := by linarith
    have hsqrtT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
    have hUj : 0 ≤ Real.sqrt (U j) := Real.sqrt_nonneg _
    positivity
  let K : ℕ → ℝ := fun j => (((A * 2 ^ j : ℕ) : ℝ) +
    (12 * Real.pi * ((A * 2 ^ j : ℕ) : ℝ) / delta) *
      (1 + Real.log S.card) +
    (S.card : ℝ) *
      (1 + 214 * Real.sqrt T +
        1536 * (((A * 2 ^ j : ℕ) : ℝ) / Real.sqrt (U j))))
  have hinner :
      ∑ j ∈ Finset.range J, K j * ‖blockCoeff (A * 2 ^ j) cn 0‖ ^ 2 ≤
        ∑ j ∈ Finset.range J, K j * E := by
    apply Finset.sum_le_sum
    intro j _hj
    have hblock : ‖blockCoeff (A * 2 ^ j) cn 0‖ ^ 2 ≤ E :=
      (norm_blockCoeff_finCoeffNat_zero_sq_le (N * M) c (A * 2 ^ j)).trans hcenergy
    exact mul_le_mul_of_nonneg_left hblock (by simpa only [K] using hfactor0 j)
  have hrangeK :
      ∑ r ∈ S,
          ‖∑ n ∈ Finset.Ico A (A * 2 ^ J), rangeTerm cn 0 (lam r) n‖ ^ 2 ≤
        (J : ℝ) * ∑ j ∈ Finset.range J,
          K j * ‖blockCoeff (A * 2 ^ j) cn 0‖ ^ 2 := by
    simpa only [K] using hrange
  refine hrangeK.trans ?_
  calc
    (J : ℝ) * ∑ j ∈ Finset.range J,
        K j * ‖blockCoeff (A * 2 ^ j) cn 0‖ ^ 2
        ≤ (J : ℝ) * ∑ j ∈ Finset.range J, K j * E :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = ((J : ℝ) * ∑ j ∈ Finset.range J, K j) * E := by
      rw [← Finset.sum_mul]
      ring
    _ = _ := by
      simp only [K, E, A, N]

/-- One divisor constant controls the same-frequency mean square of every literal grouped
Heath--Brown product multiplied by an arbitrary finite Dirichlet polynomial. -/
theorem exists_meanSquare_heathBrown_grouped_mul_dirPoly_finset
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type*} [Fintype ι] [Nonempty ι]
        (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ)
        {sigma G : ℝ}, 0 ≤ sigma →
        (∑ j : Fin (groupedDyadicUpper q),
          ‖groupedDyadicCoeffVector
            (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2 ≤ G) →
        ∀ (M : ℕ), 1 ≤ M → ∀ (b : Fin M → ℂ)
          {S : Finset ℕ} {lam : ℕ → ℝ} {delta T : ℝ},
          0 < delta → 0 ≤ T →
          (∀ i, lam i + delta ≤ lam (i + 1)) →
          (∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T) →
          ∑ r ∈ S,
              ‖(∏ i, LSeries
                (complexCoeff (arithmeticDyadicBlock
                  (heathBrownFactorBase L X (kind i)) (q i)))
                  ((sigma : ℂ) + (lam r : ℝ) * Complex.I)) *
                dirPoly M b (-lam r)‖ ^ 2 ≤
            (T + 4 * ((groupedDyadicUpper q) * M : ℕ) *
                (1 + Real.log ((groupedDyadicUpper q) * M))) *
              (1 / delta + 2 * Real.log ((groupedDyadicUpper q) * M)) *
              (C * ((((groupedDyadicUpper q) * M : ℕ) : ℝ)) ^ epsilon *
                ((((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 * G) *
                  ∑ m : Fin M, ‖b m‖ ^ 2)) := by
  obtain ⟨C, hC, hconv⟩ := exists_sum_norm_sq_dirConv_le_rpow hepsilon
  refine ⟨C, hC, ?_⟩
  intro ι instFintype instNonempty L X kind q sigma G hsigma henergy M hM b
    S lam delta T hdelta hT hgap hband
  let F : ι → ArithmeticFunction ℝ := fun i => heathBrownFactorBase L X (kind i)
  let U : ℕ := groupedDyadicUpper q
  let a : Fin U → ℂ :=
    sigmaWeightedCoeff U (groupedDyadicCoeffVector F q) sigma
  let c : Fin (U * M) → ℂ := dirConv U M a b
  let d : Fin (U * M) → ℂ := fun n => (starRingEnd ℂ) (c n)
  have hUM : 2 ≤ U * M := by
    calc
      2 = 2 * 1 := by omega
      _ ≤ U * M := Nat.mul_le_mul (two_le_groupedDyadicUpper q) hM
  have hpoint : ∀ r : ℕ,
      ‖(∏ i, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i)))
            ((sigma : ℂ) + (lam r : ℝ) * Complex.I)) *
          dirPoly M b (-lam r)‖ = ‖dirPoly (U * M) d (lam r)‖ := by
    intro r
    have hgroup :
        (∏ i, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i)))
            ((sigma : ℂ) + (lam r : ℝ) * Complex.I)) =
          dirPoly U a (-lam r) := by
      symm
      simpa only [F, U, a] using
        dirPoly_groupedDyadicCoeffVector_eq_product F q sigma (lam r)
    rw [hgroup, dirPoly_mul_eq_dirPoly]
    rw [show dirPoly (U * M) d (lam r) =
        (starRingEnd ℂ) (dirPoly (U * M) c (-lam r)) by
      exact dirPoly_conj_neg (U * M) c (lam r)]
    exact (RCLike.norm_conj _).symm
  have hmean := largeValues_dirPoly_finset (U * M) hUM d
    hdelta hT hgap hband
  have hnormd : ∑ n : Fin (U * M), ‖d n‖ ^ 2 =
      ∑ n : Fin (U * M), ‖c n‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro n _hn
    rw [RCLike.norm_conj]
  have haenergy : ∑ j : Fin U, ‖a j‖ ^ 2 ≤
      ((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 * G := by
    simpa only [F, U, a] using
      sum_normSq_sigmaWeighted_grouped_le F q hsigma henergy
  have hcenergy : ∑ n : Fin (U * M), ‖c n‖ ^ 2 ≤
      C * (((U * M : ℕ) : ℝ)) ^ epsilon *
        ((((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 * G) *
          ∑ m : Fin M, ‖b m‖ ^ 2) := by
    have hraw := hconv U M a b
    exact hraw.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right haenergy
        (Finset.sum_nonneg fun m _ => sq_nonneg ‖b m‖))
      (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)))
  have hsum :
      (∑ r ∈ S,
          ‖(∏ i, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (kind i)) (q i)))
              ((sigma : ℂ) + (lam r : ℝ) * Complex.I)) *
            dirPoly M b (-lam r)‖ ^ 2) =
        ∑ r ∈ S, ‖dirPoly (U * M) d (lam r)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro r _hr
    rw [hpoint r]
  rw [hsum]
  rw [hnormd] at hmean
  simpa only [U, Nat.cast_mul] using
    hmean.trans (mul_le_mul_of_nonneg_left hcenergy (by positivity))

/-- A fixed Perron shift only twists the grouped Heath--Brown coefficients by unit phases, so the
same convolution-energy bound controls the product with a cofactor at the unshifted ordinate. -/
theorem exists_meanSquare_heathBrown_grouped_shift_mul_dirPoly_finset
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type*} [Fintype ι] [Nonempty ι]
        (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ)
        {sigma G : ℝ}, 0 ≤ sigma →
        (∑ j : Fin (groupedDyadicUpper q),
          ‖groupedDyadicCoeffVector
            (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2 ≤ G) →
        ∀ (M : ℕ), 1 ≤ M → ∀ (b : Fin M → ℂ) (u : ℝ)
          {S : Finset ℕ} {lam : ℕ → ℝ} {delta T : ℝ},
          0 < delta → 0 ≤ T →
          (∀ i, lam i + delta ≤ lam (i + 1)) →
          (∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T) →
          ∑ r ∈ S,
              ‖(∏ i, LSeries
                (complexCoeff (arithmeticDyadicBlock
                  (heathBrownFactorBase L X (kind i)) (q i)))
                  ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I)) *
                dirPoly M b (-lam r)‖ ^ 2 ≤
            (T + 4 * ((groupedDyadicUpper q) * M : ℕ) *
                (1 + Real.log ((groupedDyadicUpper q) * M))) *
              (1 / delta + 2 * Real.log ((groupedDyadicUpper q) * M)) *
              (C * ((((groupedDyadicUpper q) * M : ℕ) : ℝ)) ^ epsilon *
                ((((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 * G) *
                  ∑ m : Fin M, ‖b m‖ ^ 2)) := by
  obtain ⟨C, hC, hconv⟩ := exists_sum_norm_sq_dirConv_le_rpow hepsilon
  refine ⟨C, hC, ?_⟩
  intro ι instFintype instNonempty L X kind q sigma G hsigma henergy M hM b u
    S lam delta T hdelta hT hgap hband
  let F : ι → ArithmeticFunction ℝ := fun i => heathBrownFactorBase L X (kind i)
  let U : ℕ := groupedDyadicUpper q
  let a0 : Fin U → ℂ :=
    sigmaWeightedCoeff U (groupedDyadicCoeffVector F q) sigma
  let a : Fin U → ℂ := fun i => a0 i *
    Complex.exp (((-u * Real.log (((i : ℕ) : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
  let c : Fin (U * M) → ℂ := dirConv U M a b
  let d : Fin (U * M) → ℂ := fun n => (starRingEnd ℂ) (c n)
  have hUM : 2 ≤ U * M := by
    calc
      2 = 2 * 1 := by omega
      _ ≤ U * M := Nat.mul_le_mul (two_le_groupedDyadicUpper q) hM
  have hpoint : ∀ r : ℕ,
      ‖(∏ i, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i)))
            ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I)) *
          dirPoly M b (-lam r)‖ = ‖dirPoly (U * M) d (lam r)‖ := by
    intro r
    have hgroup0 :
        (∏ i, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i)))
            ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I)) =
          dirPoly U a0 (-(u + lam r)) := by
      symm
      simpa only [F, U, a0] using
        dirPoly_groupedDyadicCoeffVector_eq_product F q sigma (u + lam r)
    have hshift : dirPoly U a0 (-(u + lam r)) = dirPoly U a (-lam r) := by
      have ht := dirPoly_translate U a0 (-u) (-lam r)
      rw [show -u + -lam r = -(u + lam r) by ring] at ht
      simpa only [a] using ht
    rw [hgroup0, hshift, dirPoly_mul_eq_dirPoly]
    rw [show dirPoly (U * M) d (lam r) =
        (starRingEnd ℂ) (dirPoly (U * M) c (-lam r)) by
      exact dirPoly_conj_neg (U * M) c (lam r)]
    exact (RCLike.norm_conj _).symm
  have hmean := largeValues_dirPoly_finset (U * M) hUM d
    hdelta hT hgap hband
  have hnormd : ∑ n : Fin (U * M), ‖d n‖ ^ 2 =
      ∑ n : Fin (U * M), ‖c n‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro n _hn
    rw [RCLike.norm_conj]
  have haeq : ∑ j : Fin U, ‖a j‖ ^ 2 = ∑ j : Fin U, ‖a0 j‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [show ‖a j‖ = ‖a0 j‖ by
      simpa only [a] using norm_dirPoly_twist_coeff U a0 (-u) j]
  have haenergy : ∑ j : Fin U, ‖a j‖ ^ 2 ≤
      ((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 * G := by
    rw [haeq]
    simpa only [F, U, a0] using
      sum_normSq_sigmaWeighted_grouped_le F q hsigma henergy
  have hcenergy : ∑ n : Fin (U * M), ‖c n‖ ^ 2 ≤
      C * (((U * M : ℕ) : ℝ)) ^ epsilon *
        ((((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 * G) *
          ∑ m : Fin M, ‖b m‖ ^ 2) := by
    have hraw := hconv U M a b
    exact hraw.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right haenergy
        (Finset.sum_nonneg fun m _ => sq_nonneg ‖b m‖))
      (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)))
  have hsum :
      (∑ r ∈ S,
          ‖(∏ i, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (kind i)) (q i)))
              ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I)) *
            dirPoly M b (-lam r)‖ ^ 2) =
        ∑ r ∈ S, ‖dirPoly (U * M) d (lam r)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro r _hr
    rw [hpoint r]
  rw [hsum]
  rw [hnormd] at hmean
  simpa only [U, Nat.cast_mul] using
    hmean.trans (mul_le_mul_of_nonneg_left hcenergy (by positivity))

end RHTower.Sieve
