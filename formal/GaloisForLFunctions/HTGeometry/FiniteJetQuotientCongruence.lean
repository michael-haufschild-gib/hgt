import GaloisForLFunctions.HTGeometry.InversionJetMap
import GaloisForLFunctions.HTGeometry.AsymptoticFlatHypertranscendentalInvisibility
import GaloisForLFunctions.HTGeometry.JetTaylorStructure
import GaloisForLFunctions.HTGeometry.PRecursiveDFinite

/-!
# Finite quotient-jet congruence

Finite agreement of nonvanishing smooth unit jets persists under the logarithmic derivative.
The proof composes the triangular reciprocal-jet map with Leibniz jet congruence, so it introduces
no local series expansion or analytic choice.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite unit-jet agreement transfers to finite logarithmic-derivative agreement. -/
theorem iteratedDeriv_div_jet_congr {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℂ (⊤ : ℕ∞) f U) (hg : ContDiffOn ℂ (⊤ : ℕ∞) g U)
    (hfne : ∀ w ∈ U, f w ≠ 0) (hgne : ∀ w ∈ U, g w ≠ 0) {z : ℂ} (hz : z ∈ U)
    {K : ℕ} (hjet : ∀ j ≤ K + 1, iteratedDeriv j f z = iteratedDeriv j g z) :
    ∀ k ≤ K, iteratedDeriv k (fun w => deriv f w / f w) z =
      iteratedDeriv k (fun w => deriv g w / g w) z := by
  have hfAt : ContDiffAt ℂ (⊤ : ℕ∞) f z := hf.contDiffAt (hU.mem_nhds hz)
  have hgAt : ContDiffAt ℂ (⊤ : ℕ∞) g z := hg.contDiffAt (hU.mem_nhds hz)
  have hfDeriv : ContDiffAt ℂ (⊤ : ℕ∞) (deriv f) z :=
    hfAt.derivWithin (m := (⊤ : ℕ∞)) (by simp)
  have hgDeriv : ContDiffAt ℂ (⊤ : ℕ∞) (deriv g) z :=
    hgAt.derivWithin (m := (⊤ : ℕ∞)) (by simp)
  have hinvf : ContDiffAt ℂ (⊤ : ℕ∞) (fun w => (f w)⁻¹) z :=
    (hf.inv hfne).contDiffAt (hU.mem_nhds hz)
  have hinvg : ContDiffAt ℂ (⊤ : ℕ∞) (fun w => (g w)⁻¹) z :=
    (hg.inv hgne).contDiffAt (hU.mem_nhds hz)
  have hderivJet : ∀ l ≤ K, iteratedDeriv l (deriv f) z = iteratedDeriv l (deriv g) z := by
    intro l hl
    rw [← iteratedDeriv_one, ← iteratedDeriv_one,
      GaloisForLFunctions.iteratedDeriv_iteratedDeriv,
      GaloisForLFunctions.iteratedDeriv_iteratedDeriv]
    exact hjet (l + 1) (by omega)
  have hinvJet : ∀ l ≤ K, iteratedDeriv l (fun w => (f w)⁻¹) z =
      iteratedDeriv l (fun w => (g w)⁻¹) z := by
    intro l hl
    exact iteratedDeriv_inv_jet_congr hU hf hg hfne hgne hz (K := K)
      (fun i hi => hjet i (by omega)) l hl
  have hleft : ∀ k ≤ K, iteratedDeriv k (fun w => deriv f w * (f w)⁻¹) z =
      iteratedDeriv k (fun w => deriv g w * (f w)⁻¹) z := by
    intro k hk
    simpa [mul_comm] using
      (iteratedDeriv_mul_jet_congr hfDeriv hgDeriv hinvf hderivJet hk)
  have hright : ∀ k ≤ K, iteratedDeriv k (fun w => deriv g w * (f w)⁻¹) z =
      iteratedDeriv k (fun w => deriv g w * (g w)⁻¹) z := by
    intro k hk
    simpa [mul_comm] using
      (iteratedDeriv_mul_jet_congr hinvf hinvg hgDeriv hinvJet hk)
  intro k hk
  simpa only [div_eq_mul_inv] using (hleft k hk).trans (hright k hk)

/-- Dividing the common simple coordinate shifts finite jet agreement down by one order. -/
theorem simpleZero_unit_jet_congr {u v : ℂ → ℂ}
    (hu : Differentiable ℂ u) (hv : Differentiable ℂ v) {K : ℕ}
    (hjet : ∀ j ≤ K + 1, iteratedDeriv j (fun z => z * u z) 0 =
      iteratedDeriv j (fun z => z * v z) 0) :
    ∀ k ≤ K, iteratedDeriv k u 0 = iteratedDeriv k v 0 := by
  intro k hk
  have h := hjet (k + 1) (by omega)
  rw [iteratedDeriv_id_mul_zero hu k, iteratedDeriv_id_mul_zero hv k] at h
  have hk0 : ((k : ℂ) + 1) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  apply mul_left_cancel₀ hk0
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The analytic residue-filled negative logarithmic flux of a simple-zero unit. -/
def simpleZeroResidueFlux (u : ℂ → ℂ) (x : ℂ) : ℂ :=
  -1 - x * (deriv u x / u x)

/-- Finite unit-jet agreement transfers to the residue-filled logarithmic flux. -/
theorem simpleZeroResidueFlux_jet_congr {u v : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hu : ContDiffOn ℂ (⊤ : ℕ∞) u U) (hv : ContDiffOn ℂ (⊤ : ℕ∞) v U)
    (hune : ∀ w ∈ U, u w ≠ 0) (hvne : ∀ w ∈ U, v w ≠ 0) (h0 : (0 : ℂ) ∈ U)
    {K : ℕ} (hjet : ∀ j ≤ K + 1, iteratedDeriv j u 0 = iteratedDeriv j v 0) :
    ∀ k ≤ K, iteratedDeriv k (simpleZeroResidueFlux u) 0 =
      iteratedDeriv k (simpleZeroResidueFlux v) 0 := by
  have huAt : ContDiffAt ℂ (⊤ : ℕ∞) u 0 := hu.contDiffAt (hU.mem_nhds h0)
  have hvAt : ContDiffAt ℂ (⊤ : ℕ∞) v 0 := hv.contDiffAt (hU.mem_nhds h0)
  have huDeriv : ContDiffAt ℂ (⊤ : ℕ∞) (deriv u) 0 :=
    huAt.derivWithin (m := (⊤ : ℕ∞)) (by simp)
  have hvDeriv : ContDiffAt ℂ (⊤ : ℕ∞) (deriv v) 0 :=
    hvAt.derivWithin (m := (⊤ : ℕ∞)) (by simp)
  have huq : ContDiffAt ℂ (⊤ : ℕ∞) (fun x => deriv u x / u x) 0 :=
    huDeriv.div huAt (hune 0 h0)
  have hvq : ContDiffAt ℂ (⊤ : ℕ∞) (fun x => deriv v x / v x) 0 :=
    hvDeriv.div hvAt (hvne 0 h0)
  have hquot : ∀ k ≤ K, iteratedDeriv k (fun x => deriv u x / u x) 0 =
      iteratedDeriv k (fun x => deriv v x / v x) 0 :=
    iteratedDeriv_div_jet_congr hU hu hv hune hvne h0 hjet
  have hprod : ∀ k ≤ K, iteratedDeriv k (fun x => x * (deriv u x / u x)) 0 =
      iteratedDeriv k (fun x => x * (deriv v x / v x)) 0 := by
    intro k hk
    exact iteratedDeriv_mul_jet_congr huq hvq contDiffAt_id hquot hk
  have hprodu : ContDiffAt ℂ (⊤ : ℕ∞) (fun x => x * (deriv u x / u x)) 0 :=
    contDiffAt_id.mul huq
  have hprodv : ContDiffAt ℂ (⊤ : ℕ∞) (fun x => x * (deriv v x / v x)) 0 :=
    contDiffAt_id.mul hvq
  intro k hk
  change iteratedDeriv k ((fun _ : ℂ => -1) - fun x => x * (deriv u x / u x)) 0 =
    iteratedDeriv k ((fun _ : ℂ => -1) - fun x => x * (deriv v x / v x)) 0
  rw [iteratedDeriv_sub (contDiffAt_const.of_le (by exact_mod_cast le_top))
      (hprodu.of_le (by exact_mod_cast le_top)),
    iteratedDeriv_sub (contDiffAt_const.of_le (by exact_mod_cast le_top))
      (hprodv.of_le (by exact_mod_cast le_top)), hprod k hk]

end

end GaloisForLFunctions.HTGeometry
