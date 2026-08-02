import GaloisForLFunctions.HTGeometry.GammaShiftRatioTube
import GaloisForLFunctions.HTGeometry.UniformGammaFieldIntDatum
import GaloisForLFunctions.HTGeometry.UniformGammaDatumAlgebra

/-!
# The algebra of tube data, and the tube signature (16)

The datum of eq. (4) multiplies and inverts on the tube exactly as on a line, because the shape
identities are pointwise and the `TubeLimit` calculus has the same product and inverse rules.

With the generators — a constant, a translate of `Γ`, a polynomial, a power of the vertical
logarithm — the signature `(16)` of a multi-translate monomial is computed uniformly on the tube.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {M lam : ℝ}

/-- **Tube data multiply on products.** -/
theorem HasShiftTubeDatum.mul (hlam : 0 ≤ lam) {φ χ : ℝ → ℝ → ℂ} {d : ℤ} {ω : ℝ} {b : ℤ} {c : ℂ}
    {d' : ℤ} {ω' : ℝ} {b' : ℤ} {c' : ℂ}
    (h : HasShiftTubeDatum M lam φ d ω b c) (h' : HasShiftTubeDatum M lam χ d' ω' b' c') :
    HasShiftTubeDatum M lam (fun σ t => φ σ t * χ σ t) (d + d') (ω + ω') (b + b') (c * c') := by
  refine ⟨mul_ne_zero h.1 h'.1, ?_⟩
  refine (h.2.mul h'.2).congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  have hσlam : 0 < σ + lam := by linarith
  have hS : gammaShiftShape lam σ d ω b t ≠ 0 := gammaShiftShape_ne_zero hσlam ht _ _ _
  have hS' : gammaShiftShape lam σ d' ω' b' t ≠ 0 := gammaShiftShape_ne_zero hσlam ht _ _ _
  rw [← gammaShiftShape_mul hσlam ht]
  field_simp

/-- **Inversion negates a tube datum.** -/
theorem HasShiftTubeDatum.inv (hlam : 0 ≤ lam) {φ : ℝ → ℝ → ℂ} {d : ℤ} {ω : ℝ} {b : ℤ} {c : ℂ}
    (h : HasShiftTubeDatum M lam φ d ω b c) :
    HasShiftTubeDatum M lam (fun σ t => (φ σ t)⁻¹) (-d) (-ω) (-b) c⁻¹ := by
  refine ⟨inv_ne_zero h.1, ?_⟩
  refine (h.2.inv h.1).congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  have hσlam : 0 < σ + lam := by linarith
  have hS : gammaShiftShape lam σ d ω b t ≠ 0 := gammaShiftShape_ne_zero hσlam ht _ _ _
  have hone : gammaShiftShape lam σ d ω b t * gammaShiftShape lam σ (-d) (-ω) (-b) t = 1 := by
    rw [gammaShiftShape_mul hσlam ht]
    simpa using gammaShiftShape_zero ht
  have hSinv : gammaShiftShape lam σ (-d) (-ω) (-b) t = (gammaShiftShape lam σ d ω b t)⁻¹ :=
    eq_inv_of_mul_eq_one_right hone
  rw [hSinv, inv_div_inv, inv_div]

/-- **Division subtracts tube data.** -/
theorem HasShiftTubeDatum.div (hlam : 0 ≤ lam) {φ χ : ℝ → ℝ → ℂ} {d : ℤ} {ω : ℝ} {b : ℤ} {c : ℂ}
    {d' : ℤ} {ω' : ℝ} {b' : ℤ} {c' : ℂ}
    (h : HasShiftTubeDatum M lam φ d ω b c) (h' : HasShiftTubeDatum M lam χ d' ω' b' c') :
    HasShiftTubeDatum M lam (fun σ t => φ σ t / χ σ t) (d - d') (ω - ω') (b - b') (c / c') := by
  have hmul := h.mul hlam (h'.inv hlam)
  refine ⟨div_ne_zero h.1 h'.1, ?_⟩
  have hval : c * (c' : ℂ)⁻¹ = c / c' := (div_eq_mul_inv _ _).symm
  obtain ⟨-, hlim⟩ := hmul
  rw [hval] at hlim
  refine hlim.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  show φ σ t * (χ σ t)⁻¹ / gammaShiftShape lam σ (d + -d') (ω + -ω') (b + -b') t
    = φ σ t / χ σ t / gammaShiftShape lam σ (d - d') (ω - ω') (b - b') t
  rw [← div_eq_mul_inv (φ σ t) (χ σ t), show d + -d' = d - d' by ring,
    show ω + -ω' = ω - ω' by ring, show b + -b' = b - b' by ring]

/-- **A power multiplies a tube datum.** -/
theorem HasShiftTubeDatum.pow (hlam : 0 ≤ lam) {φ : ℝ → ℝ → ℂ} {d : ℤ} {ω : ℝ} {b : ℤ} {c : ℂ}
    (h : HasShiftTubeDatum M lam φ d ω b c) (n : ℕ) :
    HasShiftTubeDatum M lam (fun σ t => φ σ t ^ n) ((n : ℤ) * d) ((n : ℝ) * ω) ((n : ℤ) * b)
      (c ^ n) := by
  induction n with
  | zero =>
      have h0 : HasShiftTubeDatum M lam (fun _ _ => (1 : ℂ)) 0 0 0 1 := by
        refine ⟨one_ne_zero, ?_⟩
        refine (tubeLimit_const (M := M) 1).congr (T₀ := 3) fun σ t hσ hσM ht => ?_
        rw [gammaShiftShape_zero ht, div_one]
      simpa using h0
  | succ n ih =>
      have hstep := ih.mul hlam h
      have hd : ((n : ℤ) * d + d) = ((n + 1 : ℕ) : ℤ) * d := by push_cast; ring
      have hω : ((n : ℝ) * ω + ω) = ((n + 1 : ℕ) : ℝ) * ω := by push_cast; ring
      have hb : ((n : ℤ) * b + b) = ((n + 1 : ℕ) : ℤ) * b := by push_cast; ring
      have hc : c ^ n * c = c ^ (n + 1) := by ring
      rw [hd, hω, hb, hc] at hstep
      refine ⟨hstep.1, ?_⟩
      refine hstep.2.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
      simp only [pow_succ]

/-- **A finite product multiplies tube data.** -/
theorem hasShiftTubeDatum_prod (hlam : 0 ≤ lam) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (φ : ι → ℝ → ℝ → ℂ) (d : ι → ℤ) (ω : ι → ℝ) (b : ι → ℤ) (c : ι → ℂ)
    (h : ∀ i ∈ s, HasShiftTubeDatum M lam (φ i) (d i) (ω i) (b i) (c i)) :
    HasShiftTubeDatum M lam (fun σ t => ∏ i ∈ s, φ i σ t) (∑ i ∈ s, d i) (∑ i ∈ s, ω i)
      (∑ i ∈ s, b i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : HasShiftTubeDatum M lam (fun _ _ => (1 : ℂ)) 0 0 0 1 := by
        refine ⟨one_ne_zero, ?_⟩
        refine (tubeLimit_const (M := M) 1).congr (T₀ := 3) fun σ t hσ hσM ht => ?_
        rw [gammaShiftShape_zero ht, div_one]
      simpa using h0
  | insert j s hj ih =>
      have hj' : HasShiftTubeDatum M lam (φ j) (d j) (ω j) (b j) (c j) :=
        h j (Finset.mem_insert_self j s)
      have hrest : ∀ i ∈ s, HasShiftTubeDatum M lam (φ i) (d i) (ω i) (b i) (c i) :=
        fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hstep := hj'.mul hlam (ih hrest)
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj,
        Finset.prod_insert hj]
      refine ⟨hstep.1, ?_⟩
      refine hstep.2.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
      simp only [Finset.prod_insert hj]

/-- A nonzero constant has the trivial tube datum. -/
theorem hasShiftTubeDatum_const {c : ℂ} (hc : c ≠ 0) :
    HasShiftTubeDatum M lam (fun _ _ => c) 0 0 0 c := by
  refine ⟨hc, ?_⟩
  refine (tubeLimit_const (M := M) c).congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  rw [gammaShiftShape_zero ht, div_one]

/-- An integer power of the vertical logarithm has tube datum `(0, 0, b)` with residue `1`. -/
theorem hasShiftTubeDatum_vertLogPow (b : ℤ) :
    HasShiftTubeDatum M lam (fun _ t => vertLog t ^ b) 0 0 b 1 := by
  refine ⟨one_ne_zero, ?_⟩
  refine (tubeLimit_const (M := M) 1).congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  have hL : vertLog t ≠ 0 := vertLog_ne_zero_of_three_le ht
  rw [gammaShiftShape, Complex.ofReal_zero, Complex.cpow_zero, zpow_zero, one_mul, one_mul,
    div_self (zpow_ne_zero _ hL)]

/-- **A nonzero polynomial has a tube datum**: its degree is the argument exponent and its leading
coefficient is the residue. -/
theorem hasShiftTubeDatum_poly {q : Polynomial ℂ} (hq : q ≠ 0) :
    HasShiftTubeDatum M lam (fun σ t => q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)) 0
      ((q.natDegree : ℕ) : ℝ) 0 q.leadingCoeff := by
  refine ⟨Polynomial.leadingCoeff_ne_zero.mpr hq, ?_⟩
  refine (tubeLimit_poly_div_pow (M := M) q).congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  have htpos : (0 : ℝ) < t := by linarith
  have hL : vertLog t ≠ 0 := vertLog_ne_zero_of_three_le ht
  refine congrArg (fun w => q.eval ((σ : ℂ) + (t : ℂ) * Complex.I) / w) ?_
  rw [gammaShiftShape, zpow_zero, zpow_zero, one_mul, mul_one,
    show (((q.natDegree : ℕ) : ℝ) : ℂ) = ((q.natDegree : ℕ) : ℂ) by push_cast; ring,
    Complex.cpow_natCast]

/-- **A Gamma translate has tube datum `(1, λ, 0)` with residue `1`** against the unshifted
reference shape: eq. (14) in datum form, uniformly on the tube. -/
theorem hasShiftTubeDatum_gammaShift (hM : 0 < M) (hlam : 0 ≤ lam) :
    HasShiftTubeDatum M 0 (fun σ t => gammaLine (σ + lam) t) 1 lam 0 1 := by
  refine ⟨one_ne_zero, ?_⟩
  refine (tubeLimit_gammaShift_ratio hM hlam).congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  refine congrArg (fun w => gammaLine (σ + lam) t / w) ?_
  rw [gammaShiftShape, add_zero, zpow_one, zpow_zero, mul_one]

/-- **The signature (16), computed uniformly on a tube.** -/
theorem hasShiftTubeDatum_multiMonomial (hM : 0 < M) {r : ℕ} (lamf : Fin r → ℝ)
    (hlam : ∀ i, 0 ≤ lamf i) (e : Fin r → ℕ) {c : ℂ} (hc : c ≠ 0)
    {q p : Polynomial ℂ} (hq : q ≠ 0) (hp : p ≠ 0) (b : ℤ) :
    HasShiftTubeDatum M 0
      (fun σ t => c * (∏ i : Fin r, gammaLine (σ + lamf i) t ^ e i)
        * (q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / p.eval ((σ : ℂ) + (t : ℂ) * Complex.I))
        * vertLog t ^ b)
      (∑ i : Fin r, (e i : ℤ))
      ((∑ i : Fin r, (e i : ℝ) * lamf i)
        + ((((q.natDegree : ℕ) : ℝ) - (((p.natDegree : ℕ) : ℝ)))))
      b (c * (q.leadingCoeff / p.leadingCoeff)) := by
  classical
  have hzero : (0 : ℝ) ≤ 0 := le_rfl
  have hconst := hasShiftTubeDatum_const (M := M) (lam := (0 : ℝ)) hc
  have hfac : ∀ i : Fin r, HasShiftTubeDatum M 0 (fun σ t => gammaLine (σ + lamf i) t ^ e i)
      ((e i : ℤ) * 1) ((e i : ℝ) * lamf i) ((e i : ℤ) * 0) (1 ^ e i) :=
    fun i => (hasShiftTubeDatum_gammaShift hM (hlam i)).pow hzero (e i)
  have hprod := hasShiftTubeDatum_prod (M := M) (lam := (0 : ℝ)) hzero Finset.univ
    (fun i σ t => gammaLine (σ + lamf i) t ^ e i)
    (fun i => (e i : ℤ) * 1) (fun i => (e i : ℝ) * lamf i) (fun i => (e i : ℤ) * 0)
    (fun i => 1 ^ e i) (fun i _ => hfac i)
  have hd : (∑ i : Fin r, (e i : ℤ) * 1) = ∑ i : Fin r, (e i : ℤ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hb0 : (∑ i : Fin r, (e i : ℤ) * 0) = 0 := by simp
  have hc1 : (∏ i : Fin r, (1 : ℂ) ^ e i) = 1 := by simp
  rw [hd, hb0, hc1] at hprod
  have hratio := (hasShiftTubeDatum_poly (M := M) (lam := (0 : ℝ)) hq).div hzero
    (hasShiftTubeDatum_poly (M := M) (lam := (0 : ℝ)) hp)
  have hlog := hasShiftTubeDatum_vertLogPow (M := M) (lam := (0 : ℝ)) b
  have hstep := ((hconst.mul hzero hprod).mul hzero hratio).mul hzero hlog
  have hdd : (0 : ℤ) + (∑ i : Fin r, (e i : ℤ)) + (0 - 0) + 0 = ∑ i : Fin r, (e i : ℤ) := by ring
  have hωω : (0 : ℝ) + (∑ i : Fin r, (e i : ℝ) * lamf i)
      + ((((q.natDegree : ℕ) : ℝ)) - (((p.natDegree : ℕ) : ℝ))) + 0
      = (∑ i : Fin r, (e i : ℝ) * lamf i)
        + ((((q.natDegree : ℕ) : ℝ)) - (((p.natDegree : ℕ) : ℝ))) := by ring
  have hbb : (0 : ℤ) + 0 + (0 - 0) + b = b := by ring
  have hcc : c * 1 * (q.leadingCoeff / p.leadingCoeff) * 1
      = c * (q.leadingCoeff / p.leadingCoeff) := by ring
  rw [hdd, hωω, hbb, hcc] at hstep
  exact hstep

end

end GaloisForLFunctions.HTGeometry
