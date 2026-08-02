import GaloisForLFunctions.HTGeometry.ShiftedJetFieldDatum
import GaloisForLFunctions.HTGeometry.GammaShiftTubeSum

/-!
# Gamma monomials with shifted polygamma coefficients

The elements of the shifted Gamma field are sums of Gamma monomials whose coefficients lie in the
shifted polygamma ring.  Each such term has a datum — the product of the coefficient's datum, which
is equation `(11)`, and the Gamma monomial's, which is the signature `(16)` — so the sum has the
datum of its dominant class whenever that class's residues do not cancel.

For a single monomial nothing can cancel, so a nonzero jet polynomial times a Gamma monomial has a
datum outright.
-/

open Filter Set Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {r : ℕ}

/-- **The datum of a Gamma monomial.** -/
theorem hasShiftTubeDatum_gammaProd {M : ℝ} (hM : 0 < M) {rr : ℕ} (lamf : Fin rr → ℝ)
    (hlamf : ∀ i, 0 ≤ lamf i) (e : Fin rr → ℕ) :
    HasShiftTubeDatum M 0 (fun σ t => ∏ i : Fin rr, gammaLine (σ + lamf i) t ^ e i)
      (∑ i : Fin rr, (e i : ℤ)) (∑ i : Fin rr, (e i : ℝ) * lamf i) 0 1 := by
  have h := hasShiftTubeDatum_multiMonomial hM lamf hlamf e (c := 1) one_ne_zero
    (q := 1) (p := 1) one_ne_zero one_ne_zero 0
  simpa using h

/-- **The datum of a Gamma monomial with a coefficient of known datum.** -/
theorem HasShiftTubeDatum.mul_gammaProd {M : ℝ} (hM : 0 < M) {rr : ℕ} (lamf : Fin rr → ℝ)
    (hlamf : ∀ i, 0 ≤ lamf i) (e : Fin rr → ℕ) {G : ℝ → ℝ → ℂ} {ω : ℝ} {b : ℤ} {c : ℂ}
    (h : HasShiftTubeDatum M 0 G 0 ω b c) :
    HasShiftTubeDatum M 0
      (fun σ t => G σ t * ∏ i : Fin rr, gammaLine (σ + lamf i) t ^ e i)
      (∑ i : Fin rr, (e i : ℤ)) (ω + ∑ i : Fin rr, (e i : ℝ) * lamf i) b c := by
  have hmul := h.mul le_rfl (hasShiftTubeDatum_gammaProd hM lamf hlamf e)
  simpa using hmul

/-- **The boundary datum of a Gamma-monomial sum with coefficients of known data.** -/
theorem exists_hasShiftTubeDatum_gammaCoeffSum {M : ℝ} (hM : 0 < M) {rr Mm : ℕ} (hMm : 0 < Mm)
    (lamf : Fin rr → ℝ) (hlamf : ∀ i, 0 ≤ lamf i) (G : Fin Mm → ℝ → ℝ → ℂ)
    (ee : Fin Mm → Fin rr → ℕ) (ω : Fin Mm → ℝ) (b : Fin Mm → ℤ) (c : Fin Mm → ℂ)
    (hdat : ∀ i, HasShiftTubeDatum M 0 (G i) 0 (ω i) (b i) (c i))
    (hclass : ∀ β : Fin Mm, (∀ α : Fin Mm,
        (∑ k : Fin rr, (ee α k : ℤ) = ∑ k : Fin rr, (ee β k : ℤ)
          ∧ ω α + ∑ k : Fin rr, (ee α k : ℝ) * lamf k
            = ω β + ∑ k : Fin rr, (ee β k : ℝ) * lamf k ∧ b α = b β)
        ∨ ShiftShapeDominates (∑ k : Fin rr, (ee β k : ℤ))
            (ω β + ∑ k : Fin rr, (ee β k : ℝ) * lamf k) (b β)
            (∑ k : Fin rr, (ee α k : ℤ))
            (ω α + ∑ k : Fin rr, (ee α k : ℝ) * lamf k) (b α)) →
      (∑ α ∈ Finset.univ.filter (fun α : Fin Mm =>
        ∑ k : Fin rr, (ee α k : ℤ) = ∑ k : Fin rr, (ee β k : ℤ)
          ∧ ω α + ∑ k : Fin rr, (ee α k : ℝ) * lamf k
            = ω β + ∑ k : Fin rr, (ee β k : ℝ) * lamf k ∧ b α = b β), c α) ≠ 0) :
    ∃ β : Fin Mm, HasShiftTubeDatum M 0
      (fun σ t => ∑ i : Fin Mm, G i σ t * ∏ k : Fin rr, gammaLine (σ + lamf k) t ^ ee i k)
      (∑ k : Fin rr, (ee β k : ℤ)) (ω β + ∑ k : Fin rr, (ee β k : ℝ) * lamf k) (b β)
      (∑ α ∈ Finset.univ.filter (fun α : Fin Mm =>
        ∑ k : Fin rr, (ee α k : ℤ) = ∑ k : Fin rr, (ee β k : ℤ)
          ∧ ω α + ∑ k : Fin rr, (ee α k : ℝ) * lamf k
            = ω β + ∑ k : Fin rr, (ee β k : ℝ) * lamf k ∧ b α = b β), c α) := by
  classical
  exact exists_hasShiftTubeDatum_sum_class hM le_rfl hMm
    (fun i σ t => G i σ t * ∏ k : Fin rr, gammaLine (σ + lamf k) t ^ ee i k)
    (fun i => ∑ k : Fin rr, (ee i k : ℤ))
    (fun i => ω i + ∑ k : Fin rr, (ee i k : ℝ) * lamf k) b c
    (fun i => (hdat i).mul_gammaProd hM lamf hlamf (ee i)) hclass

/-- **A nonzero shifted jet polynomial times a Gamma monomial has a boundary datum.**  This is the
law for a single normal-form term: equation `(11)` supplies the coefficient's residue and the
signature `(16)` supplies the Gamma part, and no cancellation is possible. -/
theorem exists_hasShiftTubeDatum_jetGammaMonomial {M : ℝ} (hM : 0 < M) {rr : ℕ}
    (lamf : Fin rr → ℝ) (hlamf : ∀ i, 0 ≤ lamf i) (e : Fin rr → ℕ)
    (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    {Mm : ℕ} (idx : Fin Mm → Fin r × ℕ) (hinj : Function.Injective idx)
    {P : MvPolynomial (Fin Mm) (Polynomial ℂ)} (hP : P ≠ 0) :
    ∃ (a b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t => jetFieldPolyFun lam idx P ((σ : ℂ) + (t : ℂ) * Complex.I)
          * ∏ k : Fin rr, gammaLine (σ + lamf k) t ^ e k)
        (∑ k : Fin rr, (e k : ℤ)) ((a : ℝ) + ∑ k : Fin rr, (e k : ℝ) * lamf k) b c := by
  obtain ⟨a, b, c, hc, hdat⟩ :=
    exists_hasShiftTubeDatum_jetFieldPolyFun lam hlam hincong idx hinj hP hM
  exact ⟨a, b, c, hc, hdat.mul_gammaProd hM lamf hlamf e⟩

end

end GaloisForLFunctions.HTGeometry
