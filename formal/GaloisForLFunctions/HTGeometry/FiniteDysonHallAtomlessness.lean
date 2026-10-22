import GaloisForLFunctions.HTGeometry.FreeFockMatrixSemicircleCoordinateLaw
import Mathlib.Combinatorics.Hall.Basic

/-!
# Hall's condition rules out atoms in solutions of a finite Dyson equation

Consider a finite index set `I`, symmetric nonnegative weights `w_ij`, and functions `g_i` on the upper
half plane satisfying the finite Dyson (quadratic vector) equation `1 + g_i(z)(z + Σ_j w_ij g_j(z)) = 0`.
If each `g_i` has an atom profile at a real point `a` (that is, `y g_i(a + iy) → i r_i` as `y → 0`), the
Dyson equation forces the balance laws `1 - r_i = r_i Σ_(j ∈ N) w_ij l_j` and `l_j Σ_(i ∈ H) w_ji r_i = 1` on
the atom support `H` and its positive-weight neighbourhood `N`. Summing gives `|H| - Σ r_i = |N|`, which
contradicts the weighted Hall condition `|N(s)| ≥ |s|` unless `H` is empty. Applied to Stieltjes
transforms of probability measures, this shows that the measures are atomless.

## Main results

- `finiteWeightHall_of_injective_positiveNeighbor`: an injective choice of positive-weight neighbours
  gives the weighted Hall condition.
- `finiteWeightHall_no_atomProfile`: under the Hall condition, the balance laws force an empty atom
  support.
- `finiteDyson_atomProfile_eq_zero`: every atom profile of a solution of the finite Dyson equation
  vanishes.
- `probabilityStieltjes_atomless_of_finiteDyson`: if the Stieltjes transforms of probability measures
  `μ_i` on `ℝ` solve the finite Dyson equation, every `μ_i` has no atoms.

## Hypotheses

Unconditional as implications. The main theorems assume symmetric nonnegative weights, the weighted
Hall condition `FiniteWeightHall w` (a combinatorial Prop on the weight graph), and that the functions
(for the last result, the Stieltjes transforms `∫ (t - z)⁻¹ dμ_i(t)`) satisfy the Dyson equation at
every `z` with `Im z > 0`. The atom-profile lemmas additionally assume the stated boundary limits
`y g_i(a + iy) → i r_i`.
-/

open Filter Topology MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The positive-weight neighbourhood of a set `s`: all `j` with `w_ij > 0` for some `i ∈ s`. -/
def positiveWeightNeighbors (w : I → I → ℝ) (s : Finset I) : Finset I :=
  Finset.univ.filter fun j ↦ ∃ i ∈ s, 0 < w i j

/-- Weighted Hall condition: every finite set has at least as many positive-weight neighbours as
elements. -/
def FiniteWeightHall (w : I → I → ℝ) : Prop :=
  ∀ s : Finset I, s.card ≤ (positiveWeightNeighbors w s).card

/-- An injective map `f` with `w_(i, f i) > 0` for all `i` gives the weighted Hall condition. -/
theorem finiteWeightHall_of_injective_positiveNeighbor
    (w : I → I → ℝ) (f : I → I) (hf : Function.Injective f)
    (hpos : ∀ i, 0 < w i (f i)) : FiniteWeightHall w := by
  intro s
  have hsubset : s.image f ⊆ positiveWeightNeighbors w s := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    rw [positiveWeightNeighbors]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, hi, hpos i⟩⟩
  calc
    s.card = (s.image f).card := (Finset.card_image_of_injective s hf).symm
    _ ≤ (positiveWeightNeighbors w s).card := Finset.card_le_card hsubset

/-- Hall obstruction: for symmetric weights under the Hall condition, real data `r, l` satisfying the two balance laws on the support `H = {r > 0}` and its neighbourhood `N` force `H = ∅`. -/
theorem finiteWeightHall_no_atomProfile
    (w : I → I → ℝ) (hsymm : ∀ i j, w i j = w j i)
    (hHall : FiniteWeightHall w) (r l : I → ℝ)
    (H : Finset I) (hH : ∀ i, i ∈ H ↔ 0 < r i)
    (N : Finset I) (hN : N = positiveWeightNeighbors w H)
    (hbalanceH : ∀ i ∈ H,
      1 - r i = r i * ∑ j ∈ N, w i j * l j)
    (hbalanceN : ∀ j ∈ N,
      l j * ∑ i ∈ H, w j i * r i = 1) :
    H = ∅ := by
  by_contra hne
  have hsumpos : 0 < ∑ i ∈ H, r i := by
    exact Finset.sum_pos (fun i hi ↦ (hH i).mp hi)
      (Finset.nonempty_iff_ne_empty.mpr hne)
  have hbalance : (H.card : ℝ) - ∑ i ∈ H, r i = N.card := by
    calc
      (H.card : ℝ) - ∑ i ∈ H, r i = ∑ i ∈ H, (1 - r i) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_const,
          nsmul_eq_mul, mul_one]
      _ = ∑ i ∈ H, r i * ∑ j ∈ N, w i j * l j := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hbalanceH i hi
      _ = ∑ j ∈ N, l j * ∑ i ∈ H, w j i * r i := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsymm i j]
        ring
      _ = ∑ j ∈ N, 1 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hbalanceN j hj
      _ = N.card := by simp
  have hlt : N.card < H.card := by
    exact_mod_cast (show (N.card : ℝ) < H.card by rw [← hbalance]; linarith)
  exact (not_lt_of_ge (by simpa [FiniteWeightHall, hN] using hHall H)) hlt

/-- The residual `1 + g_i(z)(z + Σ_j w_ij g_j(z))` of the finite Dyson equation at index `i`. -/
def finiteDysonResidual (w : I → I → ℝ) (g : I → ℂ → ℂ) (i : I) (z : ℂ) : ℂ :=
  1 + g i z * (z + ∑ j : I, (w i j : ℂ) * g j z)

omit [DecidableEq I] in
/-- Assuming the Dyson equation in the upper half plane and atom profiles `y g_i(a + iy) → i r_i`, if
`R_j = Σ_i w_ji r_i > 0` then `g_j(a + iy) / y → i / R_j` as `y → 0⁺`. -/
theorem finiteDyson_neighbor_ratio
    (w : I → I → ℝ) (g : I → ℂ → ℂ) (a : ℝ) (r : I → ℝ)
    (hres : ∀ i z, 0 < z.im → finiteDysonResidual w g i z = 0)
    (hboundary : ∀ i, Tendsto (fun y : ℝ =>
      (y : ℂ) * g i ((a : ℂ) + (y : ℂ) * Complex.I)) (𝓝[≠] 0)
        (𝓝 (Complex.I * r i)))
    (j : I) (hR : 0 < ∑ i : I, w j i * r i) :
    Tendsto (fun y : ℝ =>
      g j ((a : ℂ) + (y : ℂ) * Complex.I) / (y : ℂ)) (𝓝[>] 0)
        (𝓝 (Complex.I * (∑ i : I, w j i * r i)⁻¹)) := by
  let R : ℝ := ∑ i : I, w j i * r i
  let z : ℝ → ℂ := fun y ↦ (a : ℂ) + (y : ℂ) * Complex.I
  let D : ℝ → ℂ := fun y ↦ (y : ℂ) *
    (z y + ∑ i : I, (w j i : ℂ) * g i (z y))
  have hright_le : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := by
    apply nhdsWithin_mono
    intro y hy
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (ne_of_gt hy)
  have hzlim : Tendsto (fun y : ℝ => (y : ℂ) * z y) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun y : ℝ => (y : ℂ) * z y) 0 := by
      dsimp only [z]
      fun_prop
    change Tendsto _ (𝓝 0 ⊓ 𝓟 (Set.Ioi 0)) (𝓝 0)
    simpa [z] using hc.tendsto.mono_left inf_le_left
  have hsumlim : Tendsto (fun y : ℝ =>
      ∑ i : I, (w j i : ℂ) * ((y : ℂ) * g i (z y))) (𝓝[>] 0)
        (𝓝 (Complex.I * R)) := by
    have hsum : Tendsto (fun y : ℝ =>
        ∑ i ∈ Finset.univ, (w j i : ℂ) * ((y : ℂ) * g i (z y))) (𝓝[>] 0)
        (𝓝 (∑ i ∈ Finset.univ, (w j i : ℂ) * (Complex.I * r i))) := by
      apply tendsto_finsetSum
      intro i _
      have hi := (hboundary i).mono_left hright_le
      simpa only [z] using
        (tendsto_const_nhds.mul hi : Tendsto (fun y : ℝ =>
          (w j i : ℂ) * ((y : ℂ) * g i ((a : ℂ) + (y : ℂ) * Complex.I)))
          (𝓝[>] 0) (𝓝 ((w j i : ℂ) * (Complex.I * r i))))
    convert hsum using 1
    congr 1
    simp only [R]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hD : Tendsto D (𝓝[>] 0) (𝓝 (Complex.I * R)) := by
    have hadd := hzlim.add hsumlim
    convert hadd using 1
    · funext y
      simp only [D, mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp
  have hRne : (Complex.I * (R : ℂ)) ≠ 0 := by
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hR))
  have hinv := hD.inv₀ hRne
  have hratio : ∀ᶠ y : ℝ in 𝓝[>] 0,
      g j (z y) / (y : ℂ) = -(D y)⁻¹ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    have hd := hres j (z y) (by simpa [z] using hy)
    simp only [finiteDysonResidual] at hd
    let S : ℂ := z y + ∑ i : I, (w j i : ℂ) * g i (z y)
    have hdS : 1 + g j (z y) * S = 0 := by simpa [S] using hd
    have hprod : g j (z y) * S = -1 := by linear_combination hdS
    have hSne : S ≠ 0 := by
      intro hs
      rw [hs, mul_zero] at hprod
      norm_num at hprod
    have hg : g j (z y) = -S⁻¹ := by
      rw [show -S⁻¹ = (-1 : ℂ) / S by rw [div_eq_mul_inv]; ring]
      exact (eq_div_iff hSne).2 hprod
    rw [hg]
    change -S⁻¹ / (y : ℂ) = -((y : ℂ) * S)⁻¹
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have htarget : Tendsto (fun y ↦ -(D y)⁻¹) (𝓝[>] 0)
      (𝓝 (Complex.I * (∑ i : I, w j i * r i)⁻¹)) := by
    convert hinv.neg using 1
    simp only [R, mul_inv, Complex.inv_I]
    push_cast
    ring_nf
  exact htarget.congr' (hratio.mono fun _ h ↦ h.symm)

omit [Fintype I] [DecidableEq I] in
/-- If `y g_i(a + iy) → i r_i` with `r_i > 0`, then `Im(-g_i(a + iy)⁻¹ / y) → 1 / r_i` as `y → 0⁺`. -/
theorem finiteDyson_inverse_im_limit
    (g : I → ℂ → ℂ) (a : ℝ) (r : I → ℝ)
    (hboundary : ∀ i, Tendsto (fun y : ℝ =>
      (y : ℂ) * g i ((a : ℂ) + (y : ℂ) * Complex.I)) (𝓝[≠] 0)
        (𝓝 (Complex.I * r i)))
    (i : I) (hri : 0 < r i) :
    Tendsto (fun y : ℝ =>
      (-((g i ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹) / (y : ℂ)).im)
      (𝓝[>] 0) (𝓝 (r i)⁻¹) := by
  have hright_le : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := by
    apply nhdsWithin_mono
    intro y hy
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (ne_of_gt hy)
  have hne : Complex.I * (r i : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hri))
  have hinv := ((hboundary i).mono_left hright_le).inv₀ hne |>.neg
  have heq : ∀ᶠ y : ℝ in 𝓝[>] 0,
      -((g i ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹) / (y : ℂ) =
        -(((y : ℂ) * g i ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hcomplex : Tendsto (fun y : ℝ =>
      -((g i ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹) / (y : ℂ))
      (𝓝[>] 0) (𝓝 (Complex.I * (r i)⁻¹)) := by
    have htarget : Tendsto (fun y : ℝ =>
        -(((y : ℂ) * g i ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹))
        (𝓝[>] 0) (𝓝 (Complex.I * (r i)⁻¹)) := by
      convert hinv using 1
      simp only [mul_inv, Complex.inv_I]
      push_cast
      ring_nf
    exact htarget.congr' (heq.mono fun _ h ↦ h.symm)
  change Tendsto (Complex.im ∘ fun y : ℝ =>
    -((g i ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹) / (y : ℂ))
    (𝓝[>] 0) (𝓝 (r i)⁻¹)
  convert (Complex.continuous_im.tendsto _).comp hcomplex using 1
  simp

/-- For symmetric nonnegative weights satisfying the Hall condition, every nonnegative atom profile
`r` of a solution of the finite Dyson equation at a real point `a` is identically zero. -/
theorem finiteDyson_atomProfile_eq_zero
    (w : I → I → ℝ) (hsymm : ∀ i j, w i j = w j i)
    (hw : ∀ i j, 0 ≤ w i j) (hHall : FiniteWeightHall w)
    (g : I → ℂ → ℂ) (a : ℝ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hres : ∀ i z, 0 < z.im → finiteDysonResidual w g i z = 0)
    (hboundary : ∀ i, Tendsto (fun y : ℝ =>
      (y : ℂ) * g i ((a : ℂ) + (y : ℂ) * Complex.I)) (𝓝[≠] 0)
        (𝓝 (Complex.I * r i))) :
    ∀ i, r i = 0 := by
  let H : Finset I := Finset.univ.filter fun i ↦ 0 < r i
  let N : Finset I := positiveWeightNeighbors w H
  let R : I → ℝ := fun j ↦ ∑ i : I, w j i * r i
  let l : I → ℝ := fun j ↦ (R j)⁻¹
  have hH : ∀ i, i ∈ H ↔ 0 < r i := by intro i; simp [H]
  have hRpos : ∀ j ∈ N, 0 < R j := by
    intro j hj
    simp only [N, positiveWeightNeighbors] at hj
    obtain ⟨i, hiH, hij⟩ := (Finset.mem_filter.mp hj).2
    apply Finset.sum_pos'
    · intro k _
      exact mul_nonneg (hw j k) (hr k)
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      rw [← hsymm i j]
      exact mul_pos hij ((hH i).mp hiH)
  have hratio : ∀ j ∈ N, Tendsto (fun y : ℝ =>
      g j ((a : ℂ) + (y : ℂ) * Complex.I) / (y : ℂ)) (𝓝[>] 0)
        (𝓝 (Complex.I * l j)) := by
    intro j hj
    simpa only [l, R] using finiteDyson_neighbor_ratio
      w g a r hres hboundary j (hRpos j hj)
  have hRrestrict : ∀ j, R j = ∑ i ∈ H, w j i * r i := by
    intro j
    symm
    apply Finset.sum_subset (Finset.subset_univ H)
    intro i _ hiH
    have hnpos : ¬0 < r i := fun hpos ↦ hiH ((hH i).mpr hpos)
    have hri : r i = 0 := le_antisymm (le_of_not_gt hnpos) (hr i)
    rw [hri, mul_zero]
  have hbalanceN : ∀ j ∈ N,
      l j * ∑ i ∈ H, w j i * r i = 1 := by
    intro j hj
    rw [← hRrestrict]
    exact inv_mul_cancel₀ (ne_of_gt (hRpos j hj))
  have hbalanceH : ∀ i ∈ H,
      1 - r i = r i * ∑ j ∈ N, w i j * l j := by
    intro i hiH
    have hri : 0 < r i := (hH i).mp hiH
    have hsumlim : Tendsto (fun y : ℝ =>
        ∑ j ∈ N, w i j *
          (g j ((a : ℂ) + (y : ℂ) * Complex.I) / (y : ℂ)).im)
        (𝓝[>] 0) (𝓝 (∑ j ∈ N, w i j * l j)) := by
      apply tendsto_finsetSum
      intro j hj
      have hjim := (Complex.continuous_im.tendsto _).comp (hratio j hj)
      have hjim' : Tendsto (Complex.im ∘ fun y : ℝ =>
          g j ((a : ℂ) + (y : ℂ) * Complex.I) / (y : ℂ))
          (𝓝[>] 0) (𝓝 (l j)) := by
        convert hjim using 1
        simp
      exact tendsto_const_nhds.mul hjim'
    have hid : ∀ᶠ y : ℝ in 𝓝[>] 0,
        (-((g i ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹) / (y : ℂ)).im =
          1 + ∑ j ∈ N, w i j *
            (g j ((a : ℂ) + (y : ℂ) * Complex.I) / (y : ℂ)).im := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy0 : y ≠ 0 := ne_of_gt hy
      let z : ℂ := (a : ℂ) + (y : ℂ) * Complex.I
      let S : ℂ := z + ∑ j : I, (w i j : ℂ) * g j z
      have hd := hres i z (by simpa [z] using hy)
      simp only [finiteDysonResidual] at hd
      have hdS : 1 + g i z * S = 0 := by simpa [S] using hd
      have hprod : g i z * S = -1 := by linear_combination hdS
      have hgne : g i z ≠ 0 := by
        intro hg0
        rw [hg0, zero_mul] at hprod
        norm_num at hprod
      have hrec : -(g i z)⁻¹ = S := by
        rw [show -(g i z)⁻¹ = (-1 : ℂ) / g i z by
          rw [div_eq_mul_inv]; ring]
        apply (div_eq_iff hgne).2
        calc
          (-1 : ℂ) = g i z * S := hprod.symm
          _ = S * g i z := mul_comm _ _
      have hwzero : ∀ j ∈ Finset.univ, j ∉ N → w i j = 0 := by
        intro j _ hjN
        apply le_antisymm
        · apply le_of_not_gt
          intro hij
          apply hjN
          simp only [N, positiveWeightNeighbors]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨i, hiH, hij⟩⟩
        · exact hw i j
      have hcpx :
          -(g i z)⁻¹ / (y : ℂ) =
            ((a / y : ℝ) : ℂ) + Complex.I +
              ∑ j ∈ N, (w i j : ℂ) * (g j z / (y : ℂ)) := by
        rw [hrec]
        calc
          S / (y : ℂ) = z / (y : ℂ) +
              ∑ j : I, (w i j : ℂ) * (g j z / (y : ℂ)) := by
            simp only [S, add_div, Finset.sum_div]
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = z / (y : ℂ) +
              ∑ j ∈ N, (w i j : ℂ) * (g j z / (y : ℂ)) := by
            congr 1
            exact (Finset.sum_subset (Finset.subset_univ N) fun j hj hjN ↦ by
              rw [hwzero j hj hjN]
              norm_num).symm
          _ = ((a / y : ℝ) : ℂ) + Complex.I +
              ∑ j ∈ N, (w i j : ℂ) * (g j z / (y : ℂ)) := by
            congr 1
            dsimp only [z]
            push_cast
            field_simp [Complex.ofReal_ne_zero.mpr hy0]
      have him := congrArg Complex.im hcpx
      simpa [z] using him
    have hleft := finiteDyson_inverse_im_limit g a r hboundary i hri
    have hright : Tendsto (fun y : ℝ =>
        1 + ∑ j ∈ N, w i j *
          (g j ((a : ℂ) + (y : ℂ) * Complex.I) / (y : ℂ)).im)
        (𝓝[>] 0) (𝓝 (1 + ∑ j ∈ N, w i j * l j)) :=
      tendsto_const_nhds.add hsumlim
    have hright' := hright.congr' (hid.mono fun _ h ↦ h.symm)
    have heq := tendsto_nhds_unique hleft hright'
    field_simp [ne_of_gt hri] at heq
    linarith
  have hHem := finiteWeightHall_no_atomProfile w hsymm hHall r l H hH N rfl
    hbalanceH hbalanceN
  intro i
  have hnpos : ¬0 < r i := by
    intro hpos
    have hi : i ∈ H := (hH i).mpr hpos
    rw [hHem] at hi
    simp at hi
  exact le_antisymm (le_of_not_gt hnpos) (hr i)

/-- The Stieltjes transform `z ↦ ∫ (t - z)⁻¹ dμ_i(t)` of the probability measure `μ_i`. -/
def probabilityStieltjesTransform (μ : I → ProbabilityMeasure ℝ) (i : I) (z : ℂ) : ℂ :=
  ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂(μ i : Measure ℝ)

/-- Atomlessness: if the Stieltjes transforms of probability measures `μ_i` on `ℝ` solve the finite Dyson
equation in the upper half plane, with symmetric nonnegative weights satisfying the Hall condition, then
`μ_i {a} = 0` for every `i` and every real `a`. -/
theorem probabilityStieltjes_atomless_of_finiteDyson
    (w : I → I → ℝ) (hsymm : ∀ i j, w i j = w j i)
    (hw : ∀ i j, 0 ≤ w i j) (hHall : FiniteWeightHall w)
    (μ : I → ProbabilityMeasure ℝ)
    (hres : ∀ i z, 0 < z.im →
      finiteDysonResidual w (probabilityStieltjesTransform μ) i z = 0) :
    ∀ i a, (μ i : Measure ℝ) {a} = 0 := by
  intro i a
  let r : I → ℝ := fun j ↦ ((μ j : Measure ℝ) {a}).toReal
  have hr : ∀ j, 0 ≤ r j := fun j ↦ ENNReal.toReal_nonneg
  have hboundary : ∀ j, Tendsto (fun y : ℝ =>
      (y : ℂ) * probabilityStieltjesTransform μ j
        ((a : ℂ) + (y : ℂ) * Complex.I)) (𝓝[≠] 0)
        (𝓝 (Complex.I * r j)) := by
    intro j
    exact tendsto_mul_stieltjes_atomMass (μ j : Measure ℝ) a
  have hz := finiteDyson_atomProfile_eq_zero w hsymm hw hHall
    (probabilityStieltjesTransform μ) a r hr hres hboundary i
  exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right
    (MeasureTheory.measure_ne_top (μ i : Measure ℝ) {a})

end
end GaloisForLFunctions.HTGeometry
