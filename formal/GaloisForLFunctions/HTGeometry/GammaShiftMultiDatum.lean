import GaloisForLFunctions.HTGeometry.GammaShiftRatioGeneral

/-!
# The datum of a multi-translate monomial

With eq. (14) available every translate `Γ(s+λ_i)` has a datum in the *unshifted* reference shape —
for a shift of either sign, as long as the shifted line stays in the right half plane — so a
monomial in several translates has one too: the `Γ`-degrees add, and each translate contributes its
own shift to the real argument exponent.

That is the signature `(16)` of the shifted law, computed:

`∏ Γ(s+λ_i)^{e_i}·(q/p)·(log s)^b` has datum `(∑ e_i, ∑ e_i λ_i + deg q − deg p, b)`.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {σ lam : ℝ}

/-- **A power multiplies a datum.** -/
theorem HasShiftDatum.pow (hσ : 0 < σ + lam) {φ : ℝ → ℂ} {d : ℤ} {ω : ℝ} {b : ℤ} {c : ℂ}
    (h : HasShiftDatum lam σ φ d ω b c) (n : ℕ) :
    HasShiftDatum lam σ (fun t => φ t ^ n) ((n : ℤ) * d) ((n : ℝ) * ω) ((n : ℤ) * b) (c ^ n) := by
  induction n with
  | zero =>
      have h0 := hasShiftDatum_const (lam := lam) (σ := σ) (c := (1 : ℂ)) one_ne_zero
      simpa using h0
  | succ n ih =>
      have hstep := ih.mul hσ h
      have hd : ((n : ℤ) * d + d) = ((n + 1 : ℕ) : ℤ) * d := by push_cast; ring
      have hω : ((n : ℝ) * ω + ω) = ((n + 1 : ℕ) : ℝ) * ω := by push_cast; ring
      have hb : ((n : ℤ) * b + b) = ((n + 1 : ℕ) : ℤ) * b := by push_cast; ring
      have hc : c ^ n * c = c ^ (n + 1) := by ring
      rw [hd, hω, hb, hc] at hstep
      refine ⟨hstep.1, ?_⟩
      refine hstep.2.congr fun t => ?_
      simp only [pow_succ]

/-- **A finite product multiplies data.** -/
theorem hasShiftDatum_prod (hσ : 0 < σ + lam) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (φ : ι → ℝ → ℂ) (d : ι → ℤ) (ω : ι → ℝ) (b : ι → ℤ) (c : ι → ℂ)
    (h : ∀ i ∈ s, HasShiftDatum lam σ (φ i) (d i) (ω i) (b i) (c i)) :
    HasShiftDatum lam σ (fun t => ∏ i ∈ s, φ i t) (∑ i ∈ s, d i) (∑ i ∈ s, ω i)
      (∑ i ∈ s, b i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 := hasShiftDatum_const (lam := lam) (σ := σ) (c := (1 : ℂ)) one_ne_zero
      simpa using h0
  | insert j s hj ih =>
      have hj' : HasShiftDatum lam σ (φ j) (d j) (ω j) (b j) (c j) :=
        h j (Finset.mem_insert_self j s)
      have hrest : ∀ i ∈ s, HasShiftDatum lam σ (φ i) (d i) (ω i) (b i) (c i) :=
        fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hstep := hj'.mul hσ (ih hrest)
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj,
        Finset.prod_insert hj]
      refine ⟨hstep.1, ?_⟩
      refine hstep.2.congr fun t => ?_
      simp only [Finset.prod_insert hj]

/-- **The datum of a product of Gamma translates.**  The degrees add and each translate contributes
its shift to the real argument exponent. -/
theorem hasShiftDatum_gammaShiftProd {σ : ℝ} (hσ : 0 < σ) {r : ℕ} (lamf : Fin r → ℝ)
    (hlam : ∀ i, 0 < σ + lamf i) (e : Fin r → ℕ) :
    HasShiftDatum 0 σ (fun t => ∏ i : Fin r, gammaLine (σ + lamf i) t ^ e i)
      (∑ i : Fin r, (e i : ℤ)) (∑ i : Fin r, (e i : ℝ) * lamf i) 0 1 := by
  classical
  have hσ' : 0 < σ + 0 := by simpa using hσ
  have hfac : ∀ i : Fin r, HasShiftDatum 0 σ (fun t => gammaLine (σ + lamf i) t ^ e i)
      ((e i : ℤ) * 1) ((e i : ℝ) * lamf i) ((e i : ℤ) * 0) (1 ^ e i) :=
    fun i => (hasShiftDatum_gammaShift_general hσ (hlam i)).pow hσ' (e i)
  have hprod := hasShiftDatum_prod (lam := 0) (σ := σ) hσ' Finset.univ
    (fun i t => gammaLine (σ + lamf i) t ^ e i)
    (fun i => (e i : ℤ) * 1) (fun i => (e i : ℝ) * lamf i) (fun i => (e i : ℤ) * 0)
    (fun i => 1 ^ e i) (fun i _ => hfac i)
  have hd : (∑ i : Fin r, (e i : ℤ) * 1) = ∑ i : Fin r, (e i : ℤ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hb : (∑ i : Fin r, (e i : ℤ) * 0) = 0 := by
    simp
  have hc : (∏ i : Fin r, (1 : ℂ) ^ e i) = 1 := by
    simp
  rw [hd, hb, hc] at hprod
  exact hprod

/-- **The signature (16), computed.**  A monomial in several Gamma translates with a rational
coefficient and a logarithmic factor has the datum its degrees prescribe. -/
theorem hasShiftDatum_multiMonomial {σ : ℝ} (hσ : 0 < σ) {r : ℕ} (lamf : Fin r → ℝ)
    (hlam : ∀ i, 0 < σ + lamf i) (e : Fin r → ℕ) {c : ℂ} (hc : c ≠ 0)
    {q p : Polynomial ℂ} (hq : q ≠ 0) (hp : p ≠ 0) (b : ℤ) :
    HasShiftDatum 0 σ
      (fun t => c * (∏ i : Fin r, gammaLine (σ + lamf i) t ^ e i)
        * (q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / p.eval ((σ : ℂ) + (t : ℂ) * Complex.I))
        * vertLog t ^ b)
      (∑ i : Fin r, (e i : ℤ))
      ((∑ i : Fin r, (e i : ℝ) * lamf i)
        + ((((q.natDegree : ℕ) : ℝ) - (((p.natDegree : ℕ) : ℝ)))))
      b (c * (q.leadingCoeff / p.leadingCoeff)) := by
  classical
  have hσ' : 0 < σ + 0 := by simpa using hσ
  have hconst := hasShiftDatum_const (lam := (0 : ℝ)) (σ := σ) hc
  have hgam := hasShiftDatum_gammaShiftProd hσ lamf hlam e
  have hratio := (hasShiftDatum_poly (lam := (0 : ℝ)) hσ' hq).div hσ'
    (hasShiftDatum_poly (lam := (0 : ℝ)) hσ' hp)
  have hlog := hasShiftDatum_vertLogPow (lam := (0 : ℝ)) (σ := σ) b
  have hstep := ((hconst.mul hσ' hgam).mul hσ' hratio).mul hσ' hlog
  have hd : (0 : ℤ) + (∑ i : Fin r, (e i : ℤ)) + (0 - 0) + 0 = ∑ i : Fin r, (e i : ℤ) := by
    ring
  have hω : (0 : ℝ) + (∑ i : Fin r, (e i : ℝ) * lamf i)
      + ((((q.natDegree : ℕ) : ℝ)) - (((p.natDegree : ℕ) : ℝ))) + 0
      = (∑ i : Fin r, (e i : ℝ) * lamf i)
        + ((((q.natDegree : ℕ) : ℝ)) - (((p.natDegree : ℕ) : ℝ))) := by
    ring
  have hbb : (0 : ℤ) + 0 + (0 - 0) + b = b := by ring
  have hcc : c * 1 * (q.leadingCoeff / p.leadingCoeff) * 1
      = c * (q.leadingCoeff / p.leadingCoeff) := by ring
  rw [hd, hω, hbb, hcc] at hstep
  exact hstep

end

end GaloisForLFunctions.HTGeometry
