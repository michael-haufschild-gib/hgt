import GaloisForLFunctions.HTGeometry.KleinbockMargulis.LineChain
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.BasisDirections
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.GoodLinearChange
import GaloisForLFunctions.HTGeometry.MultilinearDiagonal
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Proposition 3.4: nondegenerate points

Near a point where the partial derivatives of `f = (f₁, …, f_n)` up to order `l` span `ℝⁿ`, every
linear combination of `1, f₁, …, f_n` is `(C, 1/dl)`-good, with one constant `C`.

For a fixed coefficient vector `w` the nondegeneracy produces an order `k ≤ l` with
`D^k (⟨w, f⟩) (x₀) ≠ 0`; symmetry of the iterated derivative turns this into a *direction* `v`
with a nonzero `k`-th directional derivative, and `exists_directions` upgrades `v` to a basis of
such directions.  In the coordinates given by that basis the hypotheses of Lemma 3.3 hold on a
neighbourhood, uniformly for coefficient vectors near `w`; `isGood_of_comp_linear_ball` transfers
the conclusion back.  Compactness of the coefficient sphere then yields one neighbourhood and one
constant.

## Main results

* `exists_local_good` — the local, one-coefficient-vector step.
-/

open Set Metric Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {d n : ℕ}

/-! ### Linear combinations of the components -/

/-- The linear functional attached to a coefficient vector. -/
noncomputable def dotCLM (w : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, w i • ContinuousLinearMap.proj i

theorem dotCLM_apply (w y : Fin n → ℝ) : dotCLM w y = ∑ i, w i * y i := by
  simp [dotCLM]

/-- The linear combination `∑ wᵢ fᵢ`. -/
noncomputable def comb (w : Fin n → ℝ) (f : (Fin d → ℝ) → (Fin n → ℝ)) :
    (Fin d → ℝ) → ℝ := fun x => ∑ i, w i * f x i

theorem comb_eq (w : Fin n → ℝ) (f : (Fin d → ℝ) → (Fin n → ℝ)) :
    comb w f = (dotCLM w) ∘ f := by
  funext x
  rw [comb, Function.comp_apply, dotCLM_apply]

theorem contDiffAt_comb {k : ℕ} {f : (Fin d → ℝ) → (Fin n → ℝ)} {y : Fin d → ℝ}
    (hf : ContDiffAt ℝ ((k : ℕ)) f y) (w : Fin n → ℝ) :
    ContDiffAt ℝ ((k : ℕ)) (comb w f) y := by
  rw [comb_eq]
  exact hf.continuousLinearMap_comp (dotCLM w)

theorem iteratedFDeriv_comb {k : ℕ} {f : (Fin d → ℝ) → (Fin n → ℝ)} {y : Fin d → ℝ}
    (hf : ContDiffAt ℝ ((k : ℕ)) f y) (w : Fin n → ℝ) (m : Fin k → (Fin d → ℝ)) :
    iteratedFDeriv ℝ k (comb w f) y m = ∑ i, w i * (iteratedFDeriv ℝ k f y m) i := by
  rw [comb_eq, ContinuousLinearMap.iteratedFDeriv_comp_left (dotCLM w) hf le_rfl]
  exact dotCLM_apply _ _

theorem iteratedFDeriv_const_add {k : ℕ} (hk : k ≠ 0) {g : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ}
    (hg : ContDiffAt ℝ ((k : ℕ)) g y) (c : ℝ) :
    iteratedFDeriv ℝ k (fun x => c + g x) y = iteratedFDeriv ℝ k g y := by
  have hfun : (fun x => c + g x) = (fun _ : Fin d → ℝ => c) + g := by
    funext x
    rfl
  rw [hfun, iteratedFDeriv_add_apply contDiffAt_const hg,
    iteratedFDeriv_const_of_ne hk]
  simp

/-! ### Continuity of the iterated derivative -/

theorem continuousAt_iteratedFDeriv {k l : ℕ} (hkl : k ≤ l) {f : (Fin d → ℝ) → (Fin n → ℝ)}
    {y : Fin d → ℝ} (hf : ContDiffAt ℝ ((l : ℕ)) f y) :
    ContinuousAt (fun z => iteratedFDeriv ℝ k f z) y := by
  have h : ContDiffAt ℝ ((0 : ℕ)) (fun z => iteratedFDeriv ℝ k f z) y := by
    refine hf.iteratedFDeriv_right ?_
    simp only [Nat.cast_zero, zero_add]
    exact_mod_cast hkl
  exact h.continuousAt

/-- The operator norm of the inverse of a linear automorphism is positive. -/
theorem norm_symm_pos [NeZero d] (T : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) :
    0 < ‖(T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))‖ := by
  rcases (norm_nonneg ((T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)))).lt_or_eq with h | h
  · exact h
  · exfalso
    have hzero : (T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) = 0 := norm_eq_zero.mp h.symm
    set e : Fin d → ℝ := fun _ => (1 : ℝ) with he
    have h1 : T.symm (T e) = e := by simp
    have h2 : T.symm (T e) = 0 := by
      show ((T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))) (T e) = 0
      rw [hzero]
      rfl
    have h3 : e = 0 := by rw [← h1, h2]
    have h4 := congrFun h3 (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d)
    rw [he] at h4
    simp at h4


/-! ### The local step -/

/-- **The local step of Proposition 3.4.**  If the `k`-th derivative of `⟨w₀, f⟩` at `x₀` does not
vanish, then all combinations with coefficient vectors near `w₀` (and an arbitrary constant term)
are `(C, 1/dk)`-good on one ball around `x₀`. -/
theorem exists_local_good [NeZero d] {l : ℕ} {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {f : (Fin d → ℝ) → (Fin n → ℝ)} (hf : ∀ y ∈ U, ContDiffAt ℝ ((l : ℕ)) f y)
    {x₀ : Fin d → ℝ} (hx₀ : x₀ ∈ U) {w₀ : Fin n → ℝ} {k : ℕ} (hk1 : 1 ≤ k) (hkl : k ≤ l)
    (hne : iteratedFDeriv ℝ k (comb w₀ f) x₀ ≠ 0) :
    ∃ (N : Set (Fin n → ℝ)) (ρ C : ℝ), N ∈ 𝓝 w₀ ∧ 0 < ρ ∧ 1 ≤ C ∧
      ∀ w ∈ N, ∀ c₀ : ℝ,
        IsGood C (((d : ℝ) * (k : ℝ))⁻¹) (fun x => c₀ + comb w f x) (ball x₀ ρ) := by
  classical
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hk0 : k ≠ 0 := by omega
  have hkR : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hα : (0:ℝ) < (((d : ℝ) * (k : ℝ))⁻¹) := by positivity
  have hfk : ∀ y ∈ U, ContDiffAt ℝ ((k : ℕ)) f y := fun y hy =>
    (hf y hy).of_le (by exact_mod_cast hkl)
  -- a direction with nonvanishing `k`-th directional derivative
  have hcd0 : ContDiffAt ℝ ((k : ℕ)) (comb w₀ f) x₀ := contDiffAt_comb (hfk x₀ hx₀) w₀
  obtain ⟨v, hv⟩ := exists_diagonal_ne_zero_of_iteratedFDeriv_ne_zero hcd0 hne
  have hΨcont : Continuous fun u : Fin d → ℝ =>
      iteratedFDeriv ℝ k (comb w₀ f) x₀ (fun _ => u) :=
    (iteratedFDeriv ℝ k (comb w₀ f) x₀).coe_continuous.comp
      (continuous_pi fun _ => continuous_id)
  obtain ⟨T, hT⟩ := exists_directions hΨcont hv
  set u : Fin d → (Fin d → ℝ) := fun i => T (Pi.single i (1 : ℝ)) with hu
  -- the sandwiched quantity
  set S : (Fin n → ℝ) × (Fin d → ℝ) → Fin d → ℝ :=
    fun p i => ∑ q, p.1 q * (iteratedFDeriv ℝ k f p.2 (fun _ => u i)) q with hS
  have hSne : ∀ i, S (w₀, x₀) i ≠ 0 := by
    intro i
    have h1 := hT i
    rw [iteratedFDeriv_comb (hfk x₀ hx₀) w₀] at h1
    exact h1
  have hScont : ∀ i, ContinuousAt (fun p => S p i) (w₀, x₀) := by
    intro i
    refine tendsto_finsetSum _ fun q _ => ?_
    refine ContinuousAt.mul ((continuous_apply q).continuousAt.comp continuousAt_fst) ?_
    refine ((continuous_apply q).continuousAt).comp ?_
    refine ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => (Fin d → ℝ))
      (Fin n → ℝ) (fun _ => u i)).continuous.continuousAt).comp ?_
    exact (continuousAt_iteratedFDeriv hkl (hf x₀ hx₀)).comp continuousAt_snd
  -- the two bounds
  set A₂ : ℝ := (Finset.univ.inf' Finset.univ_nonempty fun i => |S (w₀, x₀) i|) / 2 with hA₂def
  set A₁ : ℝ := (Finset.univ.sup' Finset.univ_nonempty fun i => |S (w₀, x₀) i|) + 1 with hA₁def
  have hA₂pos : 0 < A₂ := by
    rw [hA₂def]
    have : 0 < Finset.univ.inf' Finset.univ_nonempty fun i => |S (w₀, x₀) i| := by
      rw [Finset.lt_inf'_iff]
      intro i _
      exact abs_pos.mpr (hSne i)
    linarith
  have hA₁nn : 0 ≤ A₁ := by
    rw [hA₁def]
    have h0 : (0:ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty fun i => |S (w₀, x₀) i| := by
      obtain ⟨i⟩ := (inferInstance : Nonempty (Fin d))
      exact le_trans (abs_nonneg (S (w₀, x₀) i))
        (Finset.le_sup' (fun j => |S (w₀, x₀) j|) (Finset.mem_univ i))
    linarith
  have hev : ∀ᶠ p in 𝓝 ((w₀, x₀) : (Fin n → ℝ) × (Fin d → ℝ)),
      ∀ i, |S p i| ≤ A₁ ∧ A₂ ≤ |S p i| := by
    rw [Filter.eventually_all]
    intro i
    have hcont : ContinuousAt (fun p => |S p i|) (w₀, x₀) := (hScont i).abs
    have hup : |S (w₀, x₀) i| < A₁ := by
      rw [hA₁def]
      have := Finset.le_sup' (fun j => |S (w₀, x₀) j|) (Finset.mem_univ i)
      linarith
    have hlo : A₂ < |S (w₀, x₀) i| := by
      rw [hA₂def]
      have := Finset.inf'_le (fun j => |S (w₀, x₀) j|) (Finset.mem_univ i)
      have h2 : 0 < |S (w₀, x₀) i| := abs_pos.mpr (hSne i)
      have h3 : 0 < Finset.univ.inf' Finset.univ_nonempty fun i => |S (w₀, x₀) i| := by
        rw [Finset.lt_inf'_iff]
        intro j _
        exact abs_pos.mpr (hSne j)
      linarith
    filter_upwards [hcont.eventually (eventually_lt_nhds hup),
      hcont.eventually (eventually_gt_nhds hlo)] with p hp1 hp2
    exact ⟨hp1.le, hp2.le⟩
  -- split the neighbourhood
  rw [nhds_prod_eq, Filter.eventually_prod_iff] at hev
  obtain ⟨pa, hpa, pb, hpb, hcomb⟩ := hev
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hpb (hU.mem_nhds hx₀))
  -- Lemma 3.3 constant
  obtain ⟨K, hKpos, hK⟩ :=
    exists_isGood_of_sandwichedChains (d := d) (k := k) hdpos hk1 hA₁nn hA₂pos
  -- the radius for the transfer
  have hSpos : 0 < ‖(T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))‖ := norm_symm_pos T
  have hopenpre : IsOpen ((fun y => T y) ⁻¹' (ball x₀ r₁)) :=
    isOpen_ball.preimage T.continuous
  have hmempre : T.symm x₀ ∈ (fun y => T y) ⁻¹' (ball x₀ r₁) := by
    simp only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
    exact mem_ball_self hr₁
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.mp hopenpre _ hmempre
  refine ⟨{w | pa w}, r₂ / (2 * ‖(T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))‖),
    max 1 (K * |LinearMap.det ((T : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
      : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))| * ‖(T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))‖ ^ d),
    hpa, by positivity, le_max_left _ _, ?_⟩
  intro w hw c₀
  set g : (Fin d → ℝ) → ℝ := fun x => c₀ + comb w f x with hg
  have hgcd : ∀ y ∈ ball x₀ r₁, ContDiffAt ℝ ((k : ℕ)) g y := by
    intro y hy
    exact contDiffAt_const.add (contDiffAt_comb (hfk y (hball₁ hy).2) w)
  have hgcont : ContinuousOn g (ball x₀ r₁) := fun y hy => (hgcd y hy).continuousAt.continuousWithinAt
  have hgbd : ∀ y ∈ ball x₀ r₁, ∀ i : Fin d,
      |iteratedFDeriv ℝ k g y (fun _ => T (Pi.single i (1 : ℝ)))| ≤ A₁ ∧
      A₂ ≤ |iteratedFDeriv ℝ k g y (fun _ => T (Pi.single i (1 : ℝ)))| := by
    intro y hy i
    have hy' : y ∈ U := (hball₁ hy).2
    have heq : iteratedFDeriv ℝ k g y (fun _ => T (Pi.single i (1 : ℝ))) = S (w, y) i := by
      rw [hg, iteratedFDeriv_const_add hk0 (contDiffAt_comb (hfk y hy') w) c₀,
        iteratedFDeriv_comb (hfk y hy') w]
    rw [heq]
    exact hcomb hw (hball₁ hy).1 i
  have hsw : SandwichedChains k ((fun y => T y) ⁻¹' (ball x₀ r₁)) (g ∘ T) A₁ A₂ :=
    sandwichedChains_comp_linear hgcont hgcd T hgbd
  have hgood := hK _ _ hsw
  have hgood' : IsGood K (((d : ℝ) * (k : ℝ))⁻¹) (g ∘ T)
      (ball (T.symm x₀) (2 * ‖(T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))‖
        * (r₂ / (2 * ‖(T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))‖)))) := by
    refine hgood.mono_set ?_
    have hrw : 2 * ‖(T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))‖
        * (r₂ / (2 * ‖(T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))‖)) = r₂ := by
      field_simp
    rw [hrw]
    exact hball₂
  have hfin := isGood_of_comp_linear_ball hKpos.le T hSpos hgood'
  exact hfin.mono_const hα.le (le_max_right _ _)


/-! ### Proposition 3.4 -/

theorem norm_single_eq_one [NeZero n] (i : Fin n) :
    ‖(Pi.single i (1 : ℝ) : Fin n → ℝ)‖ = 1 := by
  refine le_antisymm (norm_single_le_one i) ?_
  have h := norm_le_pi_norm (Pi.single i (1 : ℝ) : Fin n → ℝ) i
  simpa using h

theorem comb_smul (a : ℝ) (w : Fin n → ℝ) (f : (Fin d → ℝ) → (Fin n → ℝ)) (x : Fin d → ℝ) :
    comb (a • w) f x = a * comb w f x := by
  rw [comb, comb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_assoc]

/-- **Proposition 3.4.**  At a point where the partial derivatives of `f` of order at most `l`
span `ℝⁿ`, every combination `c₀ + ∑ cᵢ fᵢ` is `(C, 1/dl)`-good on one ball, with one `C`. -/
theorem prop_3_4 [NeZero d] {l : ℕ} (hl : 1 ≤ l) {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {f : (Fin d → ℝ) → (Fin n → ℝ)} (hf : ∀ y ∈ U, ContDiffAt ℝ ((l : ℕ)) f y)
    {x₀ : Fin d → ℝ} (hx₀ : x₀ ∈ U)
    (hnd : ∀ w : Fin n → ℝ, (∀ j : ℕ, 1 ≤ j → j ≤ l → ∀ m : Fin j → (Fin d → ℝ),
        ∑ i, w i * (iteratedFDeriv ℝ j f x₀ m) i = 0) → w = 0) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ (c₀ : ℝ) (c : Fin n → ℝ),
      IsGood C (((d : ℝ) * (l : ℝ))⁻¹) (fun x => c₀ + comb c f x) (ball x₀ ρ) := by
  classical
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hlR : (0:ℝ) < (l : ℝ) := by exact_mod_cast hl
  set α : ℝ := (((d : ℝ) * (l : ℝ))⁻¹) with hαdef
  have hα : 0 < α := by rw [hαdef]; positivity
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, 1, one_pos, one_pos, fun c₀ c => ?_⟩
    refine (isGood_const hα c₀ _).congr ?_
    intro x
    simp [comb]
  haveI : NeZero n := ⟨by omega⟩
  -- the local data on the coefficient sphere
  have hlocal : ∀ w ∈ sphere (0 : Fin n → ℝ) 1, ∃ (N : Set (Fin n → ℝ)) (ρ C : ℝ),
      N ∈ 𝓝 w ∧ 0 < ρ ∧ 1 ≤ C ∧ ∀ w' ∈ N, ∀ c₀ : ℝ,
        IsGood C α (fun x => c₀ + comb w' f x) (ball x₀ ρ) := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro h
      rw [mem_sphere_zero_iff_norm, h, norm_zero] at hw
      exact zero_ne_one hw
    have hex : ∃ j : ℕ, 1 ≤ j ∧ j ≤ l ∧ iteratedFDeriv ℝ j (comb w f) x₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hw0 (hnd w fun j hj1 hjl m => ?_)
      have h1 := hcon j hj1 hjl
      have h2 : iteratedFDeriv ℝ j (comb w f) x₀ m = 0 := by rw [h1]; rfl
      rw [← iteratedFDeriv_comb ((hf x₀ hx₀).of_le (by exact_mod_cast hjl)) w m]
      exact h2
    obtain ⟨j, hj1, hjl, hjne⟩ := hex
    obtain ⟨N, ρ, C, hN, hρ, hC, hgood⟩ := exists_local_good hU hf hx₀ hj1 hjl hjne
    have hjR : (0:ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hexp : α ≤ (((d : ℝ) * (j : ℝ))⁻¹) := by
      rw [hαdef]
      have h1 : (0:ℝ) < (d : ℝ) * (j : ℝ) := by positivity
      have h2 : (d : ℝ) * (j : ℝ) ≤ (d : ℝ) * (l : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hjl) hdR.le
      simp only [← one_div]
      exact one_div_le_one_div_of_le h1 h2
    exact ⟨N, ρ, C, hN, hρ, hC,
      fun w' hw' c₀ => (hgood w' hw' c₀).mono_exponent hC hα hexp⟩
  choose! Nf ρf Cf hNf hρf hCf hgoodf using hlocal
  obtain ⟨t, hts, hcover⟩ :=
    (isCompact_sphere (0 : Fin n → ℝ) 1).elim_nhds_subcover Nf fun w hw => hNf w hw
  -- the sphere is nonempty, so the subcover is
  have hw₁ : (Pi.single (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n) (1 : ℝ))
      ∈ sphere (0 : Fin n → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact norm_single_eq_one _
  obtain ⟨w₂, hw₂t, -⟩ := Set.mem_iUnion₂.mp (hcover hw₁)
  have ht : t.Nonempty := ⟨w₂, hw₂t⟩
  set ρ : ℝ := t.inf' ht ρf with hρdef
  set C : ℝ := t.sup' ht Cf with hCdef
  have hρpos : 0 < ρ := by
    rw [hρdef, Finset.lt_inf'_iff]
    intro w hw
    exact hρf w (hts w hw)
  have hC1 : 1 ≤ C := by
    rw [hCdef]
    exact le_trans (hCf w₂ (hts w₂ hw₂t)) (Finset.le_sup' Cf hw₂t)
  refine ⟨ρ, C, hρpos, lt_of_lt_of_le one_pos hC1, ?_⟩
  intro c₀ c
  rcases eq_or_ne c 0 with rfl | hc
  · refine ((isGood_const hα c₀ (ball x₀ ρ)).congr ?_).mono_const hα.le hC1
    intro x
    simp [comb]
  · have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    set w : Fin n → ℝ := ‖c‖⁻¹ • c with hwdef
    have hwS : w ∈ sphere (0 : Fin n → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, hwdef, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (ne_of_gt hcn)]
    obtain ⟨w', hw't, hw'N⟩ := Set.mem_iUnion₂.mp (hcover hwS)
    have hg := hgoodf w' (hts w' hw't) w hw'N (c₀ / ‖c‖)
    have hg2 := hg.const_mul hα ‖c‖
    have hcw : ‖c‖ • w = c := by
      rw [hwdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hcn), one_smul]
    have hgc : IsGood (Cf w') α (fun x => c₀ + comb c f x) (ball x₀ (ρf w')) := by
      refine hg2.congr ?_
      intro x
      rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hcn), ← comb_smul, hcw]
    refine (hgc.mono_set ?_).mono_const hα.le ?_
    · exact ball_subset_ball (by rw [hρdef]; exact Finset.inf'_le ρf hw't)
    · rw [hCdef]
      exact Finset.le_sup' Cf hw't

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
