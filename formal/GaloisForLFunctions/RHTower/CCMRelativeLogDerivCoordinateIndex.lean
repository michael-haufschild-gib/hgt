import GaloisForLFunctions.RHTower.CCMEulerPickTransferBoundary

/-!
# Every active Fourier coordinate contributes one relative logarithmic negative square

For a real node `t` write `phi_t (w) = 1/(w - i t)`.  The elementary Pick identity

```text
(phi_t w + conj (phi_t v))/(w + conj v) = phi_t w * conj (phi_t v)
```

turns the partial-fraction form of the logarithmic derivative of a rational relative determinant
into an *exact signed sum of Cauchy squares*: one positive square per perturbed zero and one
negative square per genuine base pole.  The Cauchy features attached to distinct real nodes are
linearly independent — a vanishing combination has vanishing residue at each pole — so the negative
index is exactly the number of active coordinates, and no coordinate can be silently absorbed.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The Cauchy feature attached to a real node, equation `(8)`. -/
def cauchyFeature (t : ℝ) (w : ℂ) : ℂ := 1 / (w - Complex.I * (t : ℂ))

theorem conj_cauchyFeature (t : ℝ) (v : ℂ) :
    (starRingEnd ℂ) (cauchyFeature t v) = 1 / ((starRingEnd ℂ) v + Complex.I * (t : ℂ)) := by
  unfold cauchyFeature
  rw [map_div₀, map_one, map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring_nf

/-- **Equation (9).**  Each Cauchy feature is a rank-one Pick square. -/
theorem cauchyFeature_pick {t : ℝ} {w v : ℂ}
    (hw : w - Complex.I * (t : ℂ) ≠ 0)
    (hv : (starRingEnd ℂ) v + Complex.I * (t : ℂ) ≠ 0)
    (hsum : w + (starRingEnd ℂ) v ≠ 0) :
    (cauchyFeature t w + (starRingEnd ℂ) (cauchyFeature t v)) / (w + (starRingEnd ℂ) v)
      = cauchyFeature t w * (starRingEnd ℂ) (cauchyFeature t v) := by
  rw [conj_cauchyFeature]
  unfold cauchyFeature
  field_simp
  ring

/-! ## The signed Cauchy decomposition -/

/-- The partial-fraction logarithmic derivative `(7)`. -/
def relativeLogDeriv {nE nJ : ℕ} (m : Fin nE → ℝ) (e : Fin nE → ℝ) (d : Fin nJ → ℝ)
    (w : ℂ) : ℂ :=
  (∑ i, (m i : ℂ) * cauchyFeature (e i) w) - ∑ j, cauchyFeature (d j) w

/-- **Equation (10).**  The Pick kernel of the relative logarithmic derivative is an exact signed
sum of Cauchy squares: one positive square per perturbed zero, one negative square per active base
coordinate. -/
theorem relativeLogDeriv_pick_decomp {nE nJ : ℕ} (m : Fin nE → ℝ) (e : Fin nE → ℝ)
    (d : Fin nJ → ℝ) {w v : ℂ}
    (hew : ∀ i, w - Complex.I * ((e i : ℝ) : ℂ) ≠ 0)
    (hev : ∀ i, (starRingEnd ℂ) v + Complex.I * ((e i : ℝ) : ℂ) ≠ 0)
    (hdw : ∀ j, w - Complex.I * ((d j : ℝ) : ℂ) ≠ 0)
    (hdv : ∀ j, (starRingEnd ℂ) v + Complex.I * ((d j : ℝ) : ℂ) ≠ 0)
    (hsum : w + (starRingEnd ℂ) v ≠ 0) :
    (relativeLogDeriv m e d w + (starRingEnd ℂ) (relativeLogDeriv m e d v))
        / (w + (starRingEnd ℂ) v)
      = (∑ i, (m i : ℂ) * (cauchyFeature (e i) w * (starRingEnd ℂ) (cauchyFeature (e i) v)))
        - ∑ j, cauchyFeature (d j) w * (starRingEnd ℂ) (cauchyFeature (d j) v) := by
  unfold relativeLogDeriv
  rw [map_sub, map_sum, map_sum]
  have hconjm : ∀ i, (starRingEnd ℂ) ((m i : ℂ) * cauchyFeature (e i) v)
      = (m i : ℂ) * (starRingEnd ℂ) (cauchyFeature (e i) v) := by
    intro i
    rw [map_mul, Complex.conj_ofReal]
  rw [Finset.sum_congr rfl fun i _ => hconjm i]
  rw [show ((∑ i, (m i : ℂ) * cauchyFeature (e i) w) - ∑ j, cauchyFeature (d j) w
        + ((∑ i, (m i : ℂ) * (starRingEnd ℂ) (cauchyFeature (e i) v))
          - ∑ j, (starRingEnd ℂ) (cauchyFeature (d j) v)))
      = (∑ i, (m i : ℂ) * (cauchyFeature (e i) w + (starRingEnd ℂ) (cauchyFeature (e i) v)))
        - ∑ j, (cauchyFeature (d j) w + (starRingEnd ℂ) (cauchyFeature (d j) v)) from by
    simp only [mul_add, Finset.sum_add_distrib]
    ring]
  rw [sub_div, Finset.sum_div, Finset.sum_div]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_div_assoc, cauchyFeature_pick (hew i) (hev i) hsum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [cauchyFeature_pick (hdw j) (hdv j) hsum]

/-! ## Linear independence of the Cauchy features -/

/-- **Section 3, residue step.**  Multiplying by `w - i t_k` isolates the `k`-th coefficient up to
terms that vanish at the node. -/
theorem cauchyFeature_residue {n : ℕ} {t : Fin n → ℝ} {c : Fin n → ℂ} (k : Fin n) {w : ℂ}
    (hw : ∀ i, w - Complex.I * ((t i : ℝ) : ℂ) ≠ 0) :
    (w - Complex.I * ((t k : ℝ) : ℂ)) * ∑ i, c i * cauchyFeature (t i) w
      = c k + ∑ i ∈ Finset.univ.erase k,
          c i * ((w - Complex.I * ((t k : ℝ) : ℂ)) / (w - Complex.I * ((t i : ℝ) : ℂ))) := by
  classical
  have hk := hw k
  rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  congr 1
  · unfold cauchyFeature
    field_simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi := hw i
    unfold cauchyFeature
    field_simp

/-- **Section 3, independence step.**  Cauchy features attached to distinct real nodes are linearly
independent: a combination vanishing near a node has vanishing coefficient there. -/
theorem cauchyFeature_coeff_eq_zero {n : ℕ} {t : Fin n → ℝ} (ht : Function.Injective t)
    {c : Fin n → ℂ} (k : Fin n)
    (h : ∀ᶠ w in nhdsWithin (Complex.I * ((t k : ℝ) : ℂ)) {Complex.I * ((t k : ℝ) : ℂ)}ᶜ,
      (∀ i, w - Complex.I * ((t i : ℝ) : ℂ) ≠ 0)
        ∧ ∑ i, c i * cauchyFeature (t i) w = 0) :
    c k = 0 := by
  classical
  set p : ℂ := Complex.I * ((t k : ℝ) : ℂ) with hp
  have hdist : ∀ i ∈ Finset.univ.erase k, p - Complex.I * ((t i : ℝ) : ℂ) ≠ 0 := by
    intro i hi hc
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    refine hik (ht ?_)
    have hmul : Complex.I * ((t i : ℝ) : ℂ) = Complex.I * ((t k : ℝ) : ℂ) := by
      rw [hp] at hc
      linear_combination -hc
    have := mul_left_cancel₀ Complex.I_ne_zero hmul
    exact_mod_cast this
  have hcorr : Tendsto (fun w : ℂ => ∑ i ∈ Finset.univ.erase k,
      c i * ((w - p) / (w - Complex.I * ((t i : ℝ) : ℂ))))
      (nhdsWithin p {p}ᶜ) (nhds 0) := by
    have hlim : Tendsto (fun w : ℂ => ∑ i ∈ Finset.univ.erase k,
        c i * ((w - p) / (w - Complex.I * ((t i : ℝ) : ℂ))))
        (nhds p) (nhds (∑ i ∈ Finset.univ.erase k,
          c i * ((p - p) / (p - Complex.I * ((t i : ℝ) : ℂ))))) := by
      refine tendsto_finsetSum _ fun i hi => ?_
      refine Tendsto.const_mul _ ?_
      refine Tendsto.div ?_ ?_ (hdist i hi)
      · exact tendsto_id.sub tendsto_const_nhds
      · exact tendsto_id.sub tendsto_const_nhds
    have hval : (∑ i ∈ Finset.univ.erase k,
        c i * ((p - p) / (p - Complex.I * ((t i : ℝ) : ℂ)))) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [sub_self, zero_div, mul_zero]
    rw [hval] at hlim
    exact hlim.mono_left nhdsWithin_le_nhds
  have hcorr' : Tendsto (fun w : ℂ => c k + ∑ i ∈ Finset.univ.erase k,
      c i * ((w - p) / (w - Complex.I * ((t i : ℝ) : ℂ))))
      (nhdsWithin p {p}ᶜ) (nhds (c k)) := by
    have h2 := (tendsto_const_nhds (x := c k)).add hcorr
    rwa [add_zero] at h2
  have hzero : Tendsto (fun w : ℂ => c k + ∑ i ∈ Finset.univ.erase k,
      c i * ((w - p) / (w - Complex.I * ((t i : ℝ) : ℂ))))
      (nhdsWithin p {p}ᶜ) (nhds 0) := by
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℂ)))
    filter_upwards [h] with w hw
    rw [← cauchyFeature_residue k hw.1, hw.2, mul_zero]
  exact tendsto_nhds_unique hcorr' hzero

/-! ## The coordinate-count floor -/

/-- **Equation (23).**  If every integer node inside a fixed window is active, the active set has
at least `2 K + 1` elements. -/
theorem card_active_ge {J : Finset ℤ} {K : ℕ}
    (h : ∀ j : ℤ, |j| ≤ (K : ℤ) → j ∈ J) :
    2 * K + 1 ≤ J.card := by
  classical
  have hsub : Finset.Icc (-(K : ℤ)) (K : ℤ) ⊆ J := by
    intro j hj
    refine h j ?_
    rw [abs_le]
    exact ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2⟩
  have hcard : (Finset.Icc (-(K : ℤ)) (K : ℤ)).card = 2 * K + 1 := by
    rw [Int.card_Icc]
    simp
    omega
  calc 2 * K + 1 = (Finset.Icc (-(K : ℤ)) (K : ℤ)).card := hcard.symm
    _ ≤ J.card := Finset.card_le_card hsub

end GaloisForLFunctions.RHTower

end
