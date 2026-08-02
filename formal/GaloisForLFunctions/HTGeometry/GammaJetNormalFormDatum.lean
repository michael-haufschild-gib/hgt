import GaloisForLFunctions.HTGeometry.GammaJetSumDatum

/-!
# The normal-form law with no residue hypothesis

For shifts no integer combination of which is an integer, two Gamma monomials with distinct
exponent vectors can never share a signature: their argument exponents differ by an integer
combination of the shifts, and the coefficients from the shifted polygamma ring contribute only
integers.  So in a normal-form presentation the dominant class is a single term, its residue is the
residue of a nonzero element of the polygamma ring, and equation `(11)` says that is nonzero.

The datum of a normal-form sum therefore needs no hypothesis on the residues at all.
-/

open Filter Set Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {r : ℕ}

/-- No nonzero integer combination of the shifts is an integer. -/
def NoIntegerRelation {rr : ℕ} (lamf : Fin rr → ℝ) : Prop :=
  ∀ (n : Fin rr → ℤ) (m : ℤ), (∑ k : Fin rr, (n k : ℝ) * lamf k) = (m : ℝ) → ∀ k, n k = 0

/-- **The boundary datum of a normal-form Gamma sum with shifted polygamma coefficients.**  No
residue hypothesis: distinct exponent vectors have distinct signatures, so the dominant class is the
single term whose residue equation `(11)` provides. -/
theorem exists_hasShiftTubeDatum_jetGammaNormalForm {M : ℝ} (hM : 0 < M) {rr Mm K : ℕ}
    (hMm : 0 < Mm) (lamf : Fin rr → ℝ) (hlamf : ∀ k, 0 ≤ lamf k)
    (hindep : NoIntegerRelation lamf) (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    (idx : Fin K → Fin r × ℕ) (hinj : Function.Injective idx)
    (ee : Fin Mm → Fin rr → ℕ) (hee : Function.Injective ee)
    (P : Fin Mm → MvPolynomial (Fin K) (Polynomial ℂ)) (hP : ∀ i, P i ≠ 0) :
    ∃ (β : Fin Mm) (a b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t => ∑ i : Fin Mm, jetFieldPolyFun lam idx (P i) ((σ : ℂ) + (t : ℂ) * Complex.I)
          * ∏ k : Fin rr, gammaLine (σ + lamf k) t ^ ee i k)
        (∑ k : Fin rr, (ee β k : ℤ)) ((a : ℝ) + ∑ k : Fin rr, (ee β k : ℝ) * lamf k) b c := by
  classical
  choose a b c hc hdat using fun i =>
    exists_hasShiftTubeDatum_jetFieldPolyFun lam hlam hincong idx hinj (hP i) hM
  have hsingleton : ∀ β : Fin Mm,
      (Finset.univ.filter (fun α : Fin Mm =>
        ∑ k : Fin rr, (ee α k : ℤ) = ∑ k : Fin rr, (ee β k : ℤ)
          ∧ ((a α : ℤ) : ℝ) + ∑ k : Fin rr, (ee α k : ℝ) * lamf k
            = ((a β : ℤ) : ℝ) + ∑ k : Fin rr, (ee β k : ℝ) * lamf k ∧ b α = b β)) = {β} := by
    intro β
    refine Finset.ext fun α => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h2, -⟩
      have hexp : ∀ k : Fin rr, ((((ee α k : ℤ) - (ee β k : ℤ) : ℤ) : ℝ)) * lamf k
          = (ee α k : ℝ) * lamf k - (ee β k : ℝ) * lamf k := by
        intro k
        push_cast
        ring
      have hrel : (∑ k : Fin rr, ((((ee α k : ℤ) - (ee β k : ℤ) : ℤ) : ℝ)) * lamf k)
          = ((a β - a α : ℤ) : ℝ) := by
        rw [Finset.sum_congr rfl (fun k _ => hexp k), Finset.sum_sub_distrib]
        push_cast
        linarith
      have hzero := hindep (fun k => (ee α k : ℤ) - (ee β k : ℤ)) (a β - a α) hrel
      refine hee ?_
      funext k
      have hk := hzero k
      omega
    · rintro rfl
      exact ⟨rfl, rfl, rfl⟩
  obtain ⟨β, hβ⟩ := exists_hasShiftTubeDatum_gammaCoeffSum hM hMm lamf hlamf
    (fun i σ t => jetFieldPolyFun lam idx (P i) ((σ : ℂ) + (t : ℂ) * Complex.I)) ee
    (fun i => ((a i : ℤ) : ℝ)) b c hdat
    (fun β _ => by rw [hsingleton β, Finset.sum_singleton]; exact hc β)
  refine ⟨β, a β, b β, c β, hc β, ?_⟩
  have hres : (∑ α ∈ Finset.univ.filter (fun α : Fin Mm =>
      ∑ k : Fin rr, (ee α k : ℤ) = ∑ k : Fin rr, (ee β k : ℤ)
        ∧ ((a α : ℤ) : ℝ) + ∑ k : Fin rr, (ee α k : ℝ) * lamf k
          = ((a β : ℤ) : ℝ) + ∑ k : Fin rr, (ee β k : ℝ) * lamf k ∧ b α = b β), c α) = c β := by
    rw [hsingleton β, Finset.sum_singleton]
  rw [hres] at hβ
  exact hβ

/-- **The boundary datum of an arbitrary element of the shifted Gamma field.**  An element is a
quotient of two normal-form sums, and data divide. -/
theorem exists_hasShiftTubeDatum_jetGammaQuotient {M : ℝ} (hM : 0 < M) {rr Mm Mm' K : ℕ}
    (hMm : 0 < Mm) (hMm' : 0 < Mm') (lamf : Fin rr → ℝ) (hlamf : ∀ k, 0 ≤ lamf k)
    (hindep : NoIntegerRelation lamf) (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    (idx : Fin K → Fin r × ℕ) (hinj : Function.Injective idx)
    (ee : Fin Mm → Fin rr → ℕ) (hee : Function.Injective ee)
    (P : Fin Mm → MvPolynomial (Fin K) (Polynomial ℂ)) (hP : ∀ i, P i ≠ 0)
    (ee' : Fin Mm' → Fin rr → ℕ) (hee' : Function.Injective ee')
    (P' : Fin Mm' → MvPolynomial (Fin K) (Polynomial ℂ)) (hP' : ∀ i, P' i ≠ 0) :
    ∃ (d : ℤ) (ω : ℝ) (b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t =>
          (∑ i : Fin Mm, jetFieldPolyFun lam idx (P i) ((σ : ℂ) + (t : ℂ) * Complex.I)
            * ∏ k : Fin rr, gammaLine (σ + lamf k) t ^ ee i k)
          / ∑ i : Fin Mm', jetFieldPolyFun lam idx (P' i) ((σ : ℂ) + (t : ℂ) * Complex.I)
            * ∏ k : Fin rr, gammaLine (σ + lamf k) t ^ ee' i k) d ω b c := by
  obtain ⟨β, a, b, c, hc, hdat⟩ := exists_hasShiftTubeDatum_jetGammaNormalForm hM hMm lamf hlamf
    hindep lam hlam hincong idx hinj ee hee P hP
  obtain ⟨β', a', b', c', hc', hdat'⟩ := exists_hasShiftTubeDatum_jetGammaNormalForm hM hMm' lamf
    hlamf hindep lam hlam hincong idx hinj ee' hee' P' hP'
  exact ⟨_, _, _, _, div_ne_zero hc hc', hdat.div le_rfl hdat'⟩

/-- **Powers of a transcendental number have no integer relation.**  An integer relation among them
would exhibit the number as a root of a nonzero integer polynomial. -/
theorem noIntegerRelation_pow_of_transcendental {xi : ℝ} (hxi : Transcendental ℤ xi) (rr : ℕ) :
    NoIntegerRelation (fun k : Fin rr => xi ^ ((k : ℕ) + 1)) := by
  classical
  intro n m hrel k
  by_contra hk
  set P : Polynomial ℤ :=
    (∑ j : Fin rr, Polynomial.C (n j) * Polynomial.X ^ ((j : ℕ) + 1)) - Polynomial.C m with hP
  have hcoeff : P.coeff ((k : ℕ) + 1) = n k := by
    rw [hP, Polynomial.coeff_sub, Polynomial.finsetSum_coeff]
    have hterm : ∀ j : Fin rr,
        (Polynomial.C (n j) * Polynomial.X ^ ((j : ℕ) + 1)).coeff ((k : ℕ) + 1)
        = if j = k then n j else 0 := by
      intro j
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hjk : j = k
      · rw [if_pos hjk, if_pos (by rw [hjk]), mul_one]
      · have hne : ¬ ((k : ℕ) + 1 = (j : ℕ) + 1) := by
          intro h
          exact hjk (Fin.ext (by omega))
        rw [if_neg hjk, if_neg hne, mul_zero]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_eq' Finset.univ k n,
      if_pos (Finset.mem_univ k), Polynomial.coeff_C, if_neg (by omega), sub_zero]
  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0, Polynomial.coeff_zero] at hcoeff
    exact hk hcoeff.symm
  have hroot : Polynomial.aeval xi P = 0 := by
    rw [hP, map_sub, map_sum]
    have hterm : ∀ j : Fin rr,
        Polynomial.aeval xi (Polynomial.C (n j) * Polynomial.X ^ ((j : ℕ) + 1))
        = (n j : ℝ) * xi ^ ((j : ℕ) + 1) := by
      intro j
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      norm_num
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Polynomial.aeval_C]
    have hm : (algebraMap ℤ ℝ) m = (m : ℝ) := by norm_num
    rw [hm, hrel, sub_self]
  exact hxi ⟨P, hP0, hroot⟩

/-- **The shift hypotheses are inhabited at every rank.**  The powers of a Liouville number are
nonnegative and admit no integer relation. -/
theorem exists_noIntegerRelation (rr : ℕ) :
    ∃ lamf : Fin rr → ℝ, (∀ k, 0 ≤ lamf k) ∧ NoIntegerRelation lamf := by
  have hL : Liouville (liouvilleNumber ((2 : ℕ) : ℝ)) := liouville_liouvilleNumber (by norm_num)
  have hpos : (0 : ℝ) < liouvilleNumber ((2 : ℕ) : ℝ) := by
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [hcast, liouvilleNumber]
    have hs : Summable (fun i : ℕ => 1 / (2 : ℝ) ^ i.factorial) :=
      LiouvilleNumber.summable (by norm_num)
    have hle := hs.le_tsum 0 (fun i _ => by positivity)
    have h0 : (0 : ℝ) < 1 / (2 : ℝ) ^ (0 : ℕ).factorial := by norm_num
    linarith
  exact ⟨fun k => liouvilleNumber ((2 : ℕ) : ℝ) ^ ((k : ℕ) + 1),
    fun k => pow_nonneg hpos.le _, noIntegerRelation_pow_of_transcendental hL.transcendental rr⟩

/-- **The jet shift hypotheses are inhabited at every rank.**  Equally spaced shifts in `[0,1)` are
pairwise incongruent. -/
theorem exists_incongruent_shifts (r : ℕ) :
    ∃ lam : Fin r → ℝ, (∀ i, 0 ≤ lam i) ∧
      ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ) := by
  refine ⟨fun i => (i : ℝ) / (r + 1), fun i => by positivity, fun i i' hii n hn => ?_⟩
  have hden : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hreal : ((i : ℝ) / (r + 1) - (i' : ℝ) / (r + 1) : ℝ) = (n : ℝ) := by
    have hc : (((i : ℝ) / (r + 1) - (i' : ℝ) / (r + 1) : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
      push_cast
      push_cast at hn
      linear_combination hn
    exact_mod_cast hc
  have hmul : ((i : ℝ) - (i' : ℝ)) = (n : ℝ) * ((r : ℝ) + 1) := by
    field_simp at hreal
    linarith
  have hilt : (i : ℕ) < r := i.isLt
  have hi'lt : (i' : ℕ) < r := i'.isLt
  have hint : ((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ) = n * ((r : ℤ) + 1) := by
    exact_mod_cast hmul
  have hne : ((i : ℕ) : ℤ) ≠ ((i' : ℕ) : ℤ) := by
    intro h
    exact hii (Fin.ext (by exact_mod_cast h))
  rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
  · nlinarith [hint, hilt, hi'lt]
  · rw [hn0, zero_mul] at hint
    omega
  · nlinarith [hint, hilt, hi'lt]

end

end GaloisForLFunctions.HTGeometry
