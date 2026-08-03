import GaloisForLFunctions.HTGeometry.ExponentialJetSubstitution
import GaloisForLFunctions.HTGeometry.FractionRingDerivation

/-!
# The logarithmic-derivative obstruction

An exponential is never a rational function of its exponent.  Formally: if `c = A / B` were a
rational function with `c' / c` equal to a nonzero multiple of the coordinate derivative, then
`A' B - B' A = n A B`, and the left side has strictly smaller degree than the right.  So the
equation has no solution.

This is the base case of the obstruction which blocks a relation among exponentials from collapsing:
in the Artin shortening of a minimal relation among exponential monomials, the surviving
coefficients would have to satisfy exactly such a logarithmic-derivative equation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

/-- **The logarithmic-derivative equation has no polynomial solutions.**  For nonzero `A`, `B` and a
nonzero scalar `n`, the identity `A' B - B' A = n A B` is impossible: the left side has degree below
`deg A + deg B` while the right side attains it. -/
theorem derivative_mul_sub_ne_const_mul {F : Type*} [Field F] [CharZero F]
    {A B : Polynomial F} (hA : A ≠ 0) (hB : B ≠ 0) {n : F} (hn : n ≠ 0) :
    derivative A * B - derivative B * A ≠ Polynomial.C n * (A * B) := by
  intro heq
  have hABne : A * B ≠ 0 := mul_ne_zero hA hB
  have hCn : (Polynomial.C n : Polynomial F) ≠ 0 := by
    simpa using hn
  have hdegR : (Polynomial.C n * (A * B)).degree = A.degree + B.degree := by
    rw [degree_mul, degree_C hn, zero_add, degree_mul]
  have hdegA : (derivative A * B).degree < A.degree + B.degree := by
    rcases eq_or_ne (derivative A) 0 with h0 | h0
    · rw [h0, zero_mul, degree_zero]
      refine lt_of_le_of_ne bot_le ?_
      intro hcon
      have hAB : A.degree + B.degree ≠ ⊥ := by
        rw [← degree_mul]
        exact degree_ne_bot.mpr hABne
      exact hAB hcon.symm
    · rw [degree_mul]
      refine WithBot.add_lt_add_right (degree_ne_bot.mpr hB) ?_
      exact degree_derivative_lt hA
  have hdegB : (derivative B * A).degree < A.degree + B.degree := by
    rcases eq_or_ne (derivative B) 0 with h0 | h0
    · rw [h0, zero_mul, degree_zero]
      refine lt_of_le_of_ne bot_le ?_
      intro hcon
      have hAB : A.degree + B.degree ≠ ⊥ := by
        rw [← degree_mul]
        exact degree_ne_bot.mpr hABne
      exact hAB hcon.symm
    · rw [degree_mul, add_comm A.degree B.degree]
      refine WithBot.add_lt_add_right (degree_ne_bot.mpr hA) ?_
      exact degree_derivative_lt hB
  have hdegL : (derivative A * B - derivative B * A).degree < A.degree + B.degree :=
    lt_of_le_of_lt (degree_sub_le _ _) (max_lt hdegA hdegB)
  rw [heq, hdegR] at hdegL
  exact lt_irrefl _ hdegL

/-- The total jet derivation does not raise total degree: it replaces one jet variable by the next,
which has the same degree. -/
theorem totalDegree_jetTotalDerivation_le (P : MvPolynomial ℕ ℂ) :
    (jetTotalDerivation P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  refine Finset.sup_le fun s hs => ?_
  have hsdeg : (s.sum fun _ e => e) ≤ P.totalDegree := MvPolynomial.le_totalDegree hs
  rw [jetTotalDerivation, MvPolynomial.mkDerivation_monomial]
  refine le_trans (MvPolynomial.totalDegree_smul_le _ _) ?_
  rw [Finsupp.sum]
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  refine Finset.sup_le fun i hi => ?_
  have hle : Finsupp.single i 1 ≤ s := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hsum : (s.sum fun _ e => e)
      = ((s - Finsupp.single i 1).sum fun _ e => e) + 1 := by
    conv_lhs => rw [← tsub_add_cancel_of_le hle]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    congr 1
    rw [Finsupp.sum_single_index rfl]
  have hterm : (MvPolynomial.monomial (s - Finsupp.single i 1) ((s i : ℂ)) •
      (MvPolynomial.X (i + 1) : MvPolynomial ℕ ℂ)).totalDegree
      ≤ ((s - Finsupp.single i 1).sum fun _ e => e) + 1 := by
    rw [smul_eq_mul]
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    refine add_le_add (MvPolynomial.totalDegree_monomial_le _ _) ?_
    rw [MvPolynomial.totalDegree_X]
  refine le_trans hterm ?_
  rw [← hsum]
  exact hsdeg

/-- **The jet logarithmic-derivative equation is impossible.**  In the jet polynomial ring no
nonzero pair `A`, `B` satisfies `D A * B - D B * A = n * X_1 * A * B` with `n` nonzero: the total
degree of the left side is at most `deg A + deg B`, while the right side has degree one more. -/
theorem jetTotalDerivation_logDeriv_equation_impossible {A B : MvPolynomial ℕ ℂ} (hA : A ≠ 0)
    (hB : B ≠ 0) {n : ℂ} (hn : n ≠ 0) :
    jetTotalDerivation A * B - jetTotalDerivation B * A
      ≠ MvPolynomial.C n * (MvPolynomial.X 1 * (A * B)) := by
  intro heq
  have hdegL : (jetTotalDerivation A * B - jetTotalDerivation B * A).totalDegree
      ≤ A.totalDegree + B.totalDegree := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    refine max_le ?_ ?_
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      exact Nat.add_le_add_right (totalDegree_jetTotalDerivation_le A) _
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [add_comm A.totalDegree B.totalDegree]
      exact Nat.add_le_add_right (totalDegree_jetTotalDerivation_le B) _
  have hCn : (MvPolynomial.C n : MvPolynomial ℕ ℂ) ≠ 0 := by simpa using hn
  have hX1 : (MvPolynomial.X 1 : MvPolynomial ℕ ℂ) ≠ 0 := MvPolynomial.X_ne_zero 1
  have hAB : A * B ≠ 0 := mul_ne_zero hA hB
  have hdegR : (MvPolynomial.C n * (MvPolynomial.X 1 * (A * B))).totalDegree
      = 1 + (A.totalDegree + B.totalDegree) := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain hCn (mul_ne_zero hX1 hAB),
      MvPolynomial.totalDegree_mul_of_isDomain hX1 hAB,
      MvPolynomial.totalDegree_mul_of_isDomain hA hB, MvPolynomial.totalDegree_C,
      MvPolynomial.totalDegree_X, zero_add]
  rw [heq, hdegR] at hdegL
  omega

/-- A jet-like derivation: it sends each variable to a polynomial of total degree at most one. -/
def jetLikeDerivation {ι : Type*} (f : ι → MvPolynomial ι ℂ) :
    Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ) :=
  MvPolynomial.mkDerivation ℂ f

@[simp]
theorem jetLikeDerivation_X {ι : Type*} (f : ι → MvPolynomial ι ℂ) (i : ι) :
    jetLikeDerivation f (MvPolynomial.X i) = f i :=
  MvPolynomial.mkDerivation_X ℂ _ i

/-- A shift derivation on a jet polynomial ring: it sends each variable to the variable one step
along the shift. -/
def shiftDerivation {ι : Type*} (sh : ι → ι) :
    Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ) :=
  jetLikeDerivation fun i => MvPolynomial.X (sh i)

@[simp]
theorem shiftDerivation_X {ι : Type*} (sh : ι → ι) (i : ι) :
    shiftDerivation sh (MvPolynomial.X i) = MvPolynomial.X (sh i) :=
  jetLikeDerivation_X _ i

/-- **A jet-like derivation does not raise total degree.**  This covers the spectral variable, whose
derivative is the constant one, as well as the jet shift. -/
theorem totalDegree_jetLikeDerivation_le {ι : Type*} {f : ι → MvPolynomial ι ℂ}
    (hf : ∀ i, (f i).totalDegree ≤ 1) (P : MvPolynomial ι ℂ) :
    (jetLikeDerivation f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  refine Finset.sup_le fun d hd => ?_
  have hddeg : (d.sum fun _ e => e) ≤ P.totalDegree := MvPolynomial.le_totalDegree hd
  rw [jetLikeDerivation, MvPolynomial.mkDerivation_monomial]
  refine le_trans (MvPolynomial.totalDegree_smul_le _ _) ?_
  rw [Finsupp.sum]
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  refine Finset.sup_le fun i hi => ?_
  have hle : Finsupp.single i 1 ≤ d := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hsum : (d.sum fun _ e => e)
      = ((d - Finsupp.single i 1).sum fun _ e => e) + 1 := by
    conv_lhs => rw [← tsub_add_cancel_of_le hle]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    congr 1
    rw [Finsupp.sum_single_index rfl]
  have hterm : (MvPolynomial.monomial (d - Finsupp.single i 1) ((d i : ℂ)) • f i).totalDegree
      ≤ ((d - Finsupp.single i 1).sum fun _ e => e) + 1 := by
    rw [smul_eq_mul]
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    exact add_le_add (MvPolynomial.totalDegree_monomial_le _ _) (hf i)
  refine le_trans hterm ?_
  rw [← hsum]
  exact hddeg

theorem totalDegree_shiftDerivation_le {ι : Type*} (sh : ι → ι) (P : MvPolynomial ι ℂ) :
    (shiftDerivation sh P).totalDegree ≤ P.totalDegree :=
  totalDegree_jetLikeDerivation_le (fun i => le_of_eq (MvPolynomial.totalDegree_X (sh i))) P

/-- **The logarithmic-derivative equation is impossible for any jet-like derivation.**  For nonzero
`A`, `B` and a multiplier of total degree one, `D A * B - D B * A = T * (A * B)` cannot hold: the
left side has total degree at most `deg A + deg B`, the right side exactly one more. -/
theorem jetLikeDerivation_logDeriv_equation_impossible {ι : Type*} {f : ι → MvPolynomial ι ℂ}
    (hf : ∀ i, (f i).totalDegree ≤ 1) {A B T : MvPolynomial ι ℂ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hT : T ≠ 0) (hTdeg : T.totalDegree = 1) :
    jetLikeDerivation f A * B - jetLikeDerivation f B * A ≠ T * (A * B) := by
  intro heq
  have hdegL : (jetLikeDerivation f A * B - jetLikeDerivation f B * A).totalDegree
      ≤ A.totalDegree + B.totalDegree := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    refine max_le ?_ ?_
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      exact Nat.add_le_add_right (totalDegree_jetLikeDerivation_le hf A) _
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [add_comm A.totalDegree B.totalDegree]
      exact Nat.add_le_add_right (totalDegree_jetLikeDerivation_le hf B) _
  have hAB : A * B ≠ 0 := mul_ne_zero hA hB
  have hdegR : (T * (A * B)).totalDegree = 1 + (A.totalDegree + B.totalDegree) := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain hT hAB,
      MvPolynomial.totalDegree_mul_of_isDomain hA hB, hTdeg]
  rw [heq, hdegR] at hdegL
  omega

theorem shiftDerivation_logDeriv_equation_impossible {ι : Type*} (sh : ι → ι)
    {A B T : MvPolynomial ι ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (hT : T ≠ 0)
    (hTdeg : T.totalDegree = 1) :
    shiftDerivation sh A * B - shiftDerivation sh B * A ≠ T * (A * B) :=
  jetLikeDerivation_logDeriv_equation_impossible
    (fun i => le_of_eq (MvPolynomial.totalDegree_X (sh i))) hA hB hT hTdeg

/-- A jet-like derivation extended to the field of differential rational functions. -/
def jetFractionDerivation {ι : Type*} (f : ι → MvPolynomial ι ℂ) :
    Derivation ℂ (FractionRing (MvPolynomial ι ℂ)) (FractionRing (MvPolynomial ι ℂ)) :=
  GaloisForLFunctions.fractionRingDerivation
    ((Algebra.linearMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ))).compDer
      (jetLikeDerivation f))

theorem jetFractionDerivation_algebraMap {ι : Type*} (f : ι → MvPolynomial ι ℂ)
    (p : MvPolynomial ι ℂ) :
    jetFractionDerivation f (algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) p)
      = algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) (jetLikeDerivation f p) := by
  rw [jetFractionDerivation, GaloisForLFunctions.fractionRingDerivation_algebraMap]
  rfl

/-- **No differential rational function has a degree-one logarithmic derivative.**  This is the
obstruction consumed by the Artin shortening: in the field of differential rational functions, the
equation `c' = T * c` with `T` of total degree one has no nonzero solution. -/
theorem jetFraction_logDeriv_impossible {ι : Type*} {f : ι → MvPolynomial ι ℂ}
    (hf : ∀ i, (f i).totalDegree ≤ 1) {T : MvPolynomial ι ℂ}
    (hT : T ≠ 0) (hTdeg : T.totalDegree = 1)
    {c : FractionRing (MvPolynomial ι ℂ)} (hc : c ≠ 0) :
    jetFractionDerivation f c
      ≠ algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) T * c := by
  intro heq
  obtain ⟨a, b, hbmem, hab⟩ :=
    IsFractionRing.div_surjective (A := MvPolynomial ι ℂ) (K := FractionRing (MvPolynomial ι ℂ)) c
  have hb : b ≠ 0 := nonZeroDivisors.ne_zero hbmem
  have hbne : algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbmem
  have hcb : c * algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) b
      = algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) a := by
    rw [← hab, div_mul_cancel₀ _ hbne]
  have ha : a ≠ 0 := by
    intro hcon
    apply hc
    rw [← hab, hcon, map_zero, zero_div]
  have hleib := (jetFractionDerivation f).leibniz c
    (algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) b)
  rw [hcb, jetFractionDerivation_algebraMap, jetFractionDerivation_algebraMap, heq] at hleib
  simp only [smul_eq_mul] at hleib
  have hfield : algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ))
        (jetLikeDerivation f a)
      * algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) b
      = algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) T
          * (algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) a
            * algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) b)
        + algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) (jetLikeDerivation f b)
          * algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) a := by
    linear_combination
      (algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) b) * hleib
        + (algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) T
            * algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) b
          + algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ))
              (jetLikeDerivation f b)) * hcb
  have hpoly : jetLikeDerivation f a * b = T * (a * b) + jetLikeDerivation f b * a := by
    refine IsFractionRing.injective (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) ?_
    rw [map_mul, map_add, map_mul, map_mul, map_mul]
    exact hfield
  refine jetLikeDerivation_logDeriv_equation_impossible hf ha hb hT hTdeg ?_
  linear_combination hpoly

end

end GaloisForLFunctions.HTGeometry
