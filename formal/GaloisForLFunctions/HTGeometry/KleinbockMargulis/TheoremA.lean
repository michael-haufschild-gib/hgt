import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Prop23
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Reduction

/-!
# Theorem A: a nondegenerate manifold is strongly extremal

Kleinbock--Margulis, *Flows on homogeneous spaces and Diophantine approximation on manifolds*,
Theorem A: if `F : U ⊆ ℝ^d → ℝ^n` is `C^l` and nondegenerate at almost every point of `U`, then
`F x` is not very well multiplicatively approximable for almost every `x ∈ U`.

The proof is the Borel--Cantelli assembly of the two pieces already in this directory.
`prop_2_3` bounds, at a nondegenerate point, the measure of the parameters whose flowed lattice
`g_m Λ_{F x}` carries a vector shorter than `ε`; summing the resulting geometric majorant over the
multitime lattice `ℕ^n` and applying `MeasureTheory.ae_finite_setOf_mem` shows that almost every
parameter lies in only finitely many of the sets

`E_m = {x : δ(g_m Λ_{F x}) ≤ e^{-c ∑ mᵢ}}`.

`corollary_2_2` converts very well multiplicative approximability into membership in infinitely
many such sets for some `c > 0`, so the very well approximable parameters form a null set.

## Main results

* `summable_pow_sum` — `∑_{m ∈ ℕ^n} r^{∑ mᵢ} < ∞` for `0 ≤ r < 1` (a mathlib gap: there is no
  product-summability lemma for pi types).
* `NondegAt` — nondegeneracy of `F` at a point up to order `l`.
* `measure_vwma_ball_eq_zero` — the local form of Theorem A.
* `theoremA` — the global form: a null degenerate set gives a null very well approximable set.
-/

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {d n : ℕ}

/-! ### Geometric summability over the multitime lattice `ℕ^n` -/

/-- `∑_{m ∈ ℕ^n} r^{∑ mᵢ}` converges for `0 ≤ r < 1`. -/
theorem summable_pow_sum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    Summable fun m : Fin n → ℕ => r ^ (∑ i, m i) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
      have hgeo : Summable fun a : ℕ => r ^ a := summable_geometric_of_lt_one hr0 hr1
      have hf0 : (0 : ℕ → ℝ) ≤ fun a : ℕ => r ^ a := fun a => pow_nonneg hr0 a
      have hg0 : (0 : (Fin n → ℕ) → ℝ) ≤ fun m : Fin n → ℕ => r ^ (∑ i, m i) :=
        fun m => pow_nonneg hr0 _
      have hprod := Summable.mul_of_nonneg hgeo ih hf0 hg0
      refine (Equiv.summable_iff (Fin.consEquiv fun _ : Fin (n + 1) => ℕ)).mp ?_
      refine hprod.congr fun x => ?_
      have hsum : ∑ i, (Fin.consEquiv fun _ : Fin (n + 1) => ℕ) x i = x.1 + ∑ i, x.2 i := by
        simp [Fin.consEquiv]
      simp only [Function.comp_apply, hsum, pow_add]

/-! ### Nondegeneracy -/

/-- `F` is nondegenerate at `x₀` up to order `l`: no nonzero covector annihilates every
positive-order derivative of `F` at `x₀`. -/
def NondegAt (l : ℕ) (F : (Fin d → ℝ) → (Fin n → ℝ)) (x₀ : Fin d → ℝ) : Prop :=
  ∀ w : Fin n → ℝ, (∀ j : ℕ, 1 ≤ j → j ≤ l → ∀ m : Fin j → (Fin d → ℝ),
      ∑ i, w i * (iteratedFDeriv ℝ j F x₀ m) i = 0) → w = 0

/-- The parameters whose flowed lattice at multitime `m` carries a vector of norm at most
`e^{-c ∑ mᵢ}`, inside a fixed ball. -/
def shortParamSet (F : (Fin d → ℝ) → (Fin n → ℝ)) (x₀ : Fin d → ℝ) (r₀ c : ℝ)
    (m : Fin n → ℕ) : Set (Fin d → ℝ) :=
  {x ∈ ball x₀ r₀ |
    latticeDelta (flowMat (fun i => (m i : ℝ)) * unipotentMat fun i => F x i) ≤
      Real.exp (-(c * ∑ i, (m i : ℝ)))}

/-! ### The local form of Theorem A -/

theorem measure_vwma_ball_eq_zero [NeZero d] {l : ℕ} (hl : 1 ≤ l) {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) {F : (Fin d → ℝ) → (Fin n → ℝ)}
    (hF : ∀ y ∈ U, ContDiffAt ℝ ((l : ℕ)) F y)
    {x₀ : Fin d → ℝ} (hx₀ : x₀ ∈ U) (hnd : NondegAt l F x₀) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      volume {x ∈ ball x₀ r₀ | VWMA fun i => F x i} = 0 := by
  classical
  obtain ⟨r₀, D, ρ, hr₀, hD, hρ, hkey⟩ := prop_2_3 hl hU hF hx₀ hnd
  refine ⟨r₀, hr₀, ?_⟩
  set α : ℝ := (((d : ℝ) * (l : ℝ))⁻¹) with hαdef
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hα : 0 < α := by
    rw [hαdef]
    have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have hlR : (0:ℝ) < (l : ℝ) := by exact_mod_cast hl
    positivity
  set V : ℝ≥0∞ := volume (ball x₀ r₀) with hV
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  -- the null set attached to one rate `c = 1/(j+1)`
  have hnull : ∀ j : ℕ,
      volume {x | (({m : Fin n → ℕ | x ∈ shortParamSet F x₀ r₀ ((j : ℝ) + 1)⁻¹ m}).Infinite)}
        = 0 := by
    intro j
    set c : ℝ := ((j : ℝ) + 1)⁻¹ with hc
    have hcpos : 0 < c := by rw [hc]; positivity
    set rgeo : ℝ := Real.exp (-(c * α)) with hrgeo
    have hrgeo0 : 0 ≤ rgeo := (Real.exp_pos _).le
    have hrgeo1 : rgeo < 1 := by
      rw [hrgeo]
      exact Real.exp_lt_one_iff.mpr (by nlinarith)
    set B : ℝ := (D + 1) * (2 / ρ) ^ α with hB
    have hB0 : 0 ≤ B := by
      rw [hB]
      have : (0:ℝ) ≤ (2 / ρ) ^ α := Real.rpow_nonneg (by positivity) _
      nlinarith
    -- the majorant on each `E_m`
    have hmaj : ∀ m : Fin n → ℕ,
        volume (shortParamSet F x₀ r₀ c m) ≤ ENNReal.ofReal (B * rgeo ^ (∑ i, m i)) * V := by
      intro m
      set s : ℝ := ∑ i, (m i : ℝ) with hs
      have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => by positivity
      have hscast : s = ((∑ i, m i : ℕ) : ℝ) := by
        rw [hs]; push_cast; ring
      have hrpow : rgeo ^ (∑ i, m i) = Real.exp (-(c * α * s)) := by
        rw [hrgeo, ← Real.exp_nat_mul, hscast]
        ring_nf
      set ε : ℝ := 2 * Real.exp (-(c * s)) with hε
      have hεpos : 0 < ε := by rw [hε]; positivity
      have hsub : shortParamSet F x₀ r₀ c m ⊆
          {x ∈ ball x₀ r₀ |
            latticeDelta (flowMat (fun i => (m i : ℝ)) * unipotentMat fun i => F x i) < ε} := by
        rintro x ⟨hx1, hx2⟩
        refine ⟨hx1, lt_of_le_of_lt hx2 ?_⟩
        rw [hε, ← hs]
        nlinarith [Real.exp_pos (-(c * s))]
      have hexpα : (Real.exp (-(c * s))) ^ α = Real.exp (-(c * α * s)) := by
        rw [← Real.exp_mul]
        ring_nf
      by_cases hcase : ε ≤ ρ
      · have hb := hkey (fun i => (m i : ℝ)) (fun i => by positivity) ε hεpos hcase
        refine le_trans (le_trans (measure_mono hsub) hb) ?_
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (le_refl V)
        have hratio : (ε / ρ) ^ α = (2 / ρ) ^ α * Real.exp (-(c * α * s)) := by
          have hεr : ε / ρ = (2 / ρ) * Real.exp (-(c * s)) := by rw [hε]; field_simp
          rw [hεr, Real.mul_rpow (by positivity) (Real.exp_pos _).le, hexpα]
        rw [hratio, hrpow, hB]
        have hpos : (0:ℝ) ≤ (2 / ρ) ^ α * Real.exp (-(c * α * s)) := by positivity
        nlinarith
      · rw [not_le] at hcase
        have hVle : volume (shortParamSet F x₀ r₀ c m) ≤ V := by
          refine measure_mono ?_
          rintro x ⟨hx1, -⟩
          exact hx1
        refine le_trans hVle ?_
        refine le_mul_of_one_le_left' ?_
        rw [← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hrpow, hB]
        -- `ρ < ε = 2 exp(-c s)` forces `(2/ρ)^α exp(-cαs) > 1`
        have hgt : ρ / 2 < Real.exp (-(c * s)) := by rw [hε] at hcase; linarith
        have hstep : (ρ / 2) ^ α ≤ (Real.exp (-(c * s))) ^ α :=
          Real.rpow_le_rpow (by positivity) hgt.le hα.le
        rw [hexpα] at hstep
        have hmul : (2 / ρ) ^ α * (ρ / 2) ^ α = 1 := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          have : (2 / ρ) * (ρ / 2) = 1 := by field_simp
          rw [this, Real.one_rpow]
        have h2ρ : (0:ℝ) < (2 / ρ) ^ α := Real.rpow_pos_of_pos (by positivity) _
        nlinarith
    -- summability of the majorant
    have hsummable : Summable fun m : Fin n → ℕ => B * rgeo ^ (∑ i, m i) :=
      (summable_pow_sum hrgeo0 hrgeo1 n).mul_left B
    have htsum : ∑' m : Fin n → ℕ, volume (shortParamSet F x₀ r₀ c m) ≠ ⊤ := by
      have hle : ∑' m : Fin n → ℕ, volume (shortParamSet F x₀ r₀ c m) ≤
          (∑' m : Fin n → ℕ, ENNReal.ofReal (B * rgeo ^ (∑ i, m i))) * V := by
        rw [← ENNReal.tsum_mul_right]
        exact ENNReal.tsum_le_tsum hmaj
      refine ne_top_of_le_ne_top ?_ hle
      refine ENNReal.mul_ne_top ?_ hVtop
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsummable]
      exact ENNReal.ofReal_ne_top
    have hae := ae_finite_setOf_mem (μ := (volume : Measure (Fin d → ℝ)))
      (s := fun m : Fin n → ℕ => shortParamSet F x₀ r₀ c m) htsum
    rw [MeasureTheory.ae_iff] at hae
    exact hae
  -- every very well approximable parameter lies in infinitely many `E_m` for some rate
  have hcover : {x ∈ ball x₀ r₀ | VWMA fun i => F x i} ⊆
      ⋃ j : ℕ, {x | (({m : Fin n → ℕ | x ∈ shortParamSet F x₀ r₀ ((j : ℝ) + 1)⁻¹ m}).Infinite)} := by
    rintro x ⟨hxball, hxv⟩
    obtain ⟨γ, hγ, hinf⟩ := corollary_2_2 (fun i => F x i) hxv
    obtain ⟨j, hj⟩ := exists_nat_gt (1 / γ)
    have hjγ : ((j : ℝ) + 1)⁻¹ ≤ γ := by
      have hj0 : (0:ℝ) < (j : ℝ) + 1 := by positivity
      have h1 : 1 < (j : ℝ) * γ := by
        have h := hj
        rw [div_lt_iff₀ hγ] at h
        linarith
      have h2 : 1 ≤ ((j : ℝ) + 1) * γ := by nlinarith
      have h3 : ((j : ℝ) + 1)⁻¹ * (((j : ℝ) + 1) * γ) = γ := by field_simp
      calc ((j : ℝ) + 1)⁻¹ = ((j : ℝ) + 1)⁻¹ * 1 := by ring
        _ ≤ ((j : ℝ) + 1)⁻¹ * (((j : ℝ) + 1) * γ) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = γ := h3
    refine mem_iUnion.mpr ⟨j, ?_⟩
    refine Set.Infinite.mono (fun m hm => ?_) hinf
    refine ⟨hxball, ?_⟩
    refine le_trans hm ?_
    refine Real.exp_le_exp.mpr ?_
    have hsum0 : (0:ℝ) ≤ ∑ i, (m i : ℝ) := Finset.sum_nonneg fun i _ => by positivity
    nlinarith
  refine measure_mono_null hcover ?_
  exact measure_iUnion_null hnull

/-! ### The global form -/

/-- **Theorem A.**  If `F` is `C^l` on the open set `U` and the set of points of `U` at which it
is degenerate is null, then `F x` fails to be very well multiplicatively approximable for almost
every `x ∈ U`. -/
theorem theoremA [NeZero d] {l : ℕ} (hl : 1 ≤ l) {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {F : (Fin d → ℝ) → (Fin n → ℝ)} (hF : ∀ y ∈ U, ContDiffAt ℝ ((l : ℕ)) F y)
    (hdeg : volume {x ∈ U | ¬ NondegAt l F x} = 0) :
    volume {x ∈ U | VWMA fun i => F x i} = 0 := by
  classical
  have hsplit : {x ∈ U | VWMA fun i => F x i} ⊆
      {x ∈ U | ¬ NondegAt l F x} ∪ {x ∈ U | NondegAt l F x ∧ VWMA fun i => F x i} := by
    rintro x ⟨hxU, hxv⟩
    by_cases h : NondegAt l F x
    · exact Or.inr ⟨hxU, h, hxv⟩
    · exact Or.inl ⟨hxU, h⟩
  refine measure_mono_null hsplit ?_
  refine measure_union_null hdeg ?_
  refine measure_null_of_locally_null _ ?_
  rintro x ⟨hxU, hxnd, -⟩
  obtain ⟨r₀, hr₀, hnull⟩ := measure_vwma_ball_eq_zero hl hU hF hxU hxnd
  refine ⟨{y ∈ U | NondegAt l F y ∧ VWMA fun i => F y i} ∩ ball x r₀, ?_, ?_⟩
  · exact inter_mem_nhdsWithin _
      ((Metric.isOpen_ball : IsOpen (ball x r₀)).mem_nhds (mem_ball_self hr₀))
  · refine measure_mono_null (fun y hy => ?_) hnull
    exact ⟨hy.2, hy.1.2.2⟩

/-- **Theorem A, all-order form.**  If `F` is `C^l` for every `l` and the set of points at which
`F` is degenerate at *every* finite order is null, then almost every parameter is not very well
multiplicatively approximable.  This is the form to use when the nondegeneracy order is not
uniform over the parameter space. -/
theorem theoremA_allOrders [NeZero d] {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {F : (Fin d → ℝ) → (Fin n → ℝ)} (hF : ∀ y ∈ U, ∀ l : ℕ, ContDiffAt ℝ ((l : ℕ)) F y)
    (hdeg : volume {x ∈ U | ∀ l : ℕ, 1 ≤ l → ¬ NondegAt l F x} = 0) :
    volume {x ∈ U | VWMA fun i => F x i} = 0 := by
  classical
  have hsplit : {x ∈ U | VWMA fun i => F x i} ⊆
      {x ∈ U | ∀ l : ℕ, 1 ≤ l → ¬ NondegAt l F x} ∪
        ⋃ l : ℕ, {x ∈ U | NondegAt (l + 1) F x ∧ VWMA fun i => F x i} := by
    rintro x ⟨hxU, hxv⟩
    by_cases h : ∀ l : ℕ, 1 ≤ l → ¬ NondegAt l F x
    · exact Or.inl ⟨hxU, h⟩
    · refine Or.inr ?_
      have hex : ∃ l : ℕ, 1 ≤ l ∧ NondegAt l F x := by
        by_contra hc
        exact h fun l hl hnd => hc ⟨l, hl, hnd⟩
      obtain ⟨l, hl, hnd⟩ := hex
      refine mem_iUnion.mpr ⟨l - 1, ?_⟩
      have hl1 : l - 1 + 1 = l := by omega
      rw [hl1]
      exact ⟨hxU, hnd, hxv⟩
  refine measure_mono_null hsplit ?_
  refine measure_union_null hdeg ?_
  refine measure_iUnion_null fun l => ?_
  refine measure_null_of_locally_null _ ?_
  rintro x ⟨hxU, hxnd, -⟩
  obtain ⟨r₀, hr₀, hnull⟩ :=
    measure_vwma_ball_eq_zero (l := l + 1) (by omega) hU (fun y hy => hF y hy (l + 1)) hxU hxnd
  refine ⟨{y ∈ U | NondegAt (l + 1) F y ∧ VWMA (fun i => F y i)} ∩ ball x r₀, ?_, ?_⟩
  · exact inter_mem_nhdsWithin _
      ((Metric.isOpen_ball : IsOpen (ball x r₀)).mem_nhds (mem_ball_self hr₀))
  · refine measure_mono_null (fun y hy => ?_) hnull
    exact ⟨hy.2, hy.1.2.2⟩

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
