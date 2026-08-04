import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import GaloisForLFunctions.HTGeometry.HilbertSchmidt

/-!
# Weak transfer of a boundary-strip budget

The boundary-strip transfer theorem has three ingredients, and this module proves all three
unconditionally.  None of them mentions `Xi`, primes, or any conjecture.

* `norm_le_of_weak_limit` — **weak lower semicontinuity in the usable form**: if `A n` converges
  weakly to `x` and `‖A n‖ ≤ c` eventually, then `‖x‖ ≤ c`.  This is what the card's step "weak lower
  semicontinuity of the Hilbert–Schmidt norm" needs, applied in the Hilbert space `S_2`.  Stated with
  an eventual bound rather than a `liminf`, because that is exactly the shape of the four-unit
  hypothesis `(7)`.
* `eq_of_graphCore` — **the graph-core extension**, equations `(4)`–`(5)`: a continuous map that agrees
  with `Q ∘ D` on a graph core agrees with it on the whole domain.  The graph core is the entire
  content: only the existence, for each `f`, of approximants converging *together with their images*
  under `D` is used.
* `eventually_div_le_one_add_of_le_fourMulCDF` — **the four-unit asymptotics**, equations `(8)`–`(9)`:
  a profile bounded by `4(1 - e^{-u}) + r(u)` with `r(u) = o(u)` has
  `limsup_(u -> 0+) Delta(u)/(4(1 - e^{-u})) <= 1`.  The `limsup` is stated in its epsilon form, which
  avoids extended-real junk values and is what a consumer uses.

The kernel-model half of the same transfer is already in the tree as
`RHTower.hsNormSq_le_of_tendsto_entries` (entrywise lower semicontinuity of the Hilbert–Schmidt
energy); this module supplies the abstract-operator half.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology Set

/-! ## Weak lower semicontinuity -/

/-- **Weak lower semicontinuity of the norm.**  A weak limit inherits every eventual norm bound.  The
proof is Cauchy–Schwarz against the limit itself: `‖x‖² = lim ⟪x, A n⟫ ≤ ‖x‖ c`. -/
theorem norm_le_of_weak_limit {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {x : K} {A : ℕ → K} {c : ℝ}
    (hw : Tendsto (fun n => (inner ℝ x (A n) : ℝ)) atTop (𝓝 ((inner ℝ x x : ℝ))))
    (hb : ∀ᶠ n in atTop, ‖A n‖ ≤ c) : ‖x‖ ≤ c := by
  rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
  · -- the zero vector inherits any bound, since `c` is then nonnegative
    have hc : 0 ≤ c := by
      obtain ⟨n, hn⟩ := hb.exists
      exact le_trans (norm_nonneg (A n)) hn
    rw [← hx]
    exact hc
  · have hkey : (inner ℝ x x : ℝ) ≤ ‖x‖ * c := by
      refine le_of_tendsto hw ?_
      filter_upwards [hb] with n hn
      calc (inner ℝ x (A n) : ℝ) ≤ ‖x‖ * ‖A n‖ := real_inner_le_norm x (A n)
        _ ≤ ‖x‖ * c := by
            exact mul_le_mul_of_nonneg_left hn (norm_nonneg x)
    rw [real_inner_self_eq_norm_mul_norm] at hkey
    exact le_of_mul_le_mul_left (by linarith [hkey]) hx

/-! ## The graph-core extension -/

/-- **Equations (4)–(5).**  A continuous map agreeing with `Q ∘ D` on a graph core agrees with it
everywhere.  Only the graph-core approximation property is used: for each `f` there are approximants
in `C` converging to `f` *together with* their `D`-images. -/
theorem eq_of_graphCore {H K K' : Type*} [TopologicalSpace H] [TopologicalSpace K]
    [TopologicalSpace K'] [T2Space K'] {T : H → K'} {Q : K → K'} {Dop : H → K} {C : Set H}
    (hT : Continuous T) (hQ : Continuous Q)
    (hC : ∀ f ∈ C, T f = Q (Dop f)) {f : H}
    (hcore : ∃ g : ℕ → H, (∀ j, g j ∈ C) ∧ Tendsto g atTop (𝓝 f)
      ∧ Tendsto (fun j => Dop (g j)) atTop (𝓝 (Dop f))) :
    T f = Q (Dop f) := by
  obtain ⟨g, hgC, hgf, hgD⟩ := hcore
  have h1 : Tendsto (fun j => T (g j)) atTop (𝓝 (T f)) := (hT.tendsto f).comp hgf
  have h2 : Tendsto (fun j => Q (Dop (g j))) atTop (𝓝 (Q (Dop f))) := (hQ.tendsto _).comp hgD
  refine tendsto_nhds_unique ?_ h2
  exact h1.congr fun j => hC (g j) (hgC j)

/-! ## The four-unit asymptotics -/

/-- The incoming Euler-pole profile `4(1 - e^{-u})` is positive on the positive ray. -/
theorem fourMulCDF_pos {u : ℝ} (hu : 0 < u) : 0 < 4 * (1 - Real.exp (-u)) := by
  have h : Real.exp (-u) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  linarith

/-- The slope of `1 - e^{-u}` at the origin is one. -/
theorem tendsto_one_sub_exp_neg_div :
    Tendsto (fun u : ℝ => (1 - Real.exp (-u)) / u) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have hd : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u)) 1 0 := by
    have h0 : HasDerivAt (fun u : ℝ => -u) (-1) 0 := hasDerivAt_neg 0
    have h1 := HasDerivAt.exp h0
    have h3 := HasDerivAt.const_sub (1 : ℝ) h1
    have hval : -(Real.exp (-(0 : ℝ)) * (-1)) = (1 : ℝ) := by norm_num
    rw [hval] at h3
    exact h3
  rw [hasDerivAt_iff_tendsto_slope] at hd
  refine hd.congr fun u => ?_
  simp only [slope, vsub_eq_sub, sub_zero]
  norm_num
  rw [div_eq_inv_mul]

/-- The reciprocal profile ratio tends to `1/4`. -/
theorem tendsto_div_fourMulCDF :
    Tendsto (fun u : ℝ => u / (4 * (1 - Real.exp (-u)))) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 4)) := by
  have h4 : Tendsto (fun u : ℝ => 4 * ((1 - Real.exp (-u)) / u)) (𝓝[≠] (0 : ℝ)) (𝓝 4) := by
    simpa using tendsto_one_sub_exp_neg_div.const_mul (4 : ℝ)
  have hinv : Tendsto (fun u : ℝ => 1 / (4 * ((1 - Real.exp (-u)) / u))) (𝓝[≠] (0 : ℝ))
      (𝓝 (1 / 4)) := tendsto_const_nhds.div h4 (by norm_num)
  refine hinv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hune : u ≠ 0 := by simpa using hu
  have hdne : (1 - Real.exp (-u)) ≠ 0 := by
    intro hc
    have h1 : Real.exp (-u) = 1 := by linarith
    rw [Real.exp_eq_one_iff] at h1
    exact hune (by linarith)
  field_simp

/-- **Equations (8)–(9).**  A profile under the four-unit budget with an `o(u)` remainder has
one-sided ratio at most one in the limit.  This is `limsup_(u -> 0+) Delta(u)/(4(1-e^{-u})) <= 1`,
written in the epsilon form that avoids extended-real junk values. -/
theorem eventually_div_le_one_add_of_le_fourMulCDF {Delta r : ℝ → ℝ}
    (hrem : Tendsto (fun u : ℝ => r u / u) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hbudget : ∀ u : ℝ, 0 < u → Delta u ≤ 4 * (1 - Real.exp (-u)) + r u)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u in 𝓝[>] (0 : ℝ), Delta u / (4 * (1 - Real.exp (-u))) ≤ 1 + ε := by
  have hsub : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) := by
    refine nhdsWithin_mono 0 ?_
    intro v hv
    exact ne_of_gt hv
  have hratio : Tendsto (fun u : ℝ => (r u / u) * (u / (4 * (1 - Real.exp (-u)))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hrem.mul (tendsto_div_fourMulCDF.mono_left hsub)
    simpa using h
  have hsmall : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      (r u / u) * (u / (4 * (1 - Real.exp (-u)))) ≤ ε := by
    have h := hratio.eventually (Iio_mem_nhds hε)
    exact h.mono fun u hu => le_of_lt hu
  filter_upwards [hsmall, self_mem_nhdsWithin] with u hu hupos
  have hpos : 0 < u := hupos
  have hden : 0 < 4 * (1 - Real.exp (-u)) := fourMulCDF_pos hpos
  have hsplit : (r u / u) * (u / (4 * (1 - Real.exp (-u))))
      = r u / (4 * (1 - Real.exp (-u))) := by
    field_simp
  rw [hsplit] at hu
  rw [div_le_iff₀ hden]
  have hb := hbudget u hpos
  calc Delta u ≤ 4 * (1 - Real.exp (-u)) + r u := hb
    _ ≤ 4 * (1 - Real.exp (-u)) + ε * (4 * (1 - Real.exp (-u))) := by
        have : r u ≤ ε * (4 * (1 - Real.exp (-u))) := by
          rw [← div_le_iff₀ hden]
          exact hu
        linarith
    _ = (1 + ε) * (4 * (1 - Real.exp (-u))) := by ring

/-! ## Equation (3) in the Hilbert–Schmidt realisation -/

/-- The complex form of weak lower semicontinuity.  The real part of the pairing is used rather than
its norm, because the `RCLike` cast of `‖x‖²` does not match either `Complex.norm_real` or
`RCLike.norm_ofReal`. -/
theorem norm_le_of_weak_limit_complex {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {x : K} {A : ℕ → K} {c : ℝ}
    (hw : Tendsto (fun n => (inner ℂ x (A n) : ℂ)) atTop (𝓝 ((inner ℂ x x : ℂ))))
    (hb : ∀ᶠ n in atTop, ‖A n‖ ≤ c) : ‖x‖ ≤ c := by
  rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
  · have hc : 0 ≤ c := by
      obtain ⟨n, hn⟩ := hb.exists
      exact le_trans (norm_nonneg (A n)) hn
    rw [← hx]
    exact hc
  · have hre : Tendsto (fun n => RCLike.re (inner ℂ x (A n) : ℂ)) atTop
        (𝓝 (RCLike.re (inner ℂ x x : ℂ))) := (RCLike.continuous_re.tendsto _).comp hw
    have hkey : RCLike.re (inner ℂ x x : ℂ) ≤ ‖x‖ * c := by
      refine le_of_tendsto hre ?_
      filter_upwards [hb] with n hn
      calc RCLike.re (inner ℂ x (A n) : ℂ) ≤ ‖(inner ℂ x (A n) : ℂ)‖ := RCLike.re_le_norm _
        _ ≤ ‖x‖ * ‖A n‖ := norm_inner_le_norm x (A n)
        _ ≤ ‖x‖ * c := mul_le_mul_of_nonneg_left hn (norm_nonneg x)
    rw [inner_self_eq_norm_mul_norm] at hkey
    exact le_of_mul_le_mul_left (by linarith [hkey]) hx

/-- **Equation (3).**  A family of Hilbert–Schmidt kernels whose pairings against the limit converge
and whose energies are eventually at most `B` has a limit of energy at most `B`.  This is the abstract
transfer theorem in the corpus's `lp 2` realisation of `S_2`: no weak compactness, no norm convergence
of the operators, and no trace-class property is used. -/
theorem hsNormSq_le_of_weak_limit {ι : Type*} {K : ι × ι → ℂ}
    (hK : _root_.HilbertSchmidt.IsHS K)
    {A : ℕ → ι × ι → ℂ} (hA : ∀ n, _root_.HilbertSchmidt.IsHS (A n)) {B : ℝ}
    (hw : Tendsto (fun n => _root_.HilbertSchmidt.hsInner K (A n)) atTop
      (𝓝 (_root_.HilbertSchmidt.hsInner K K)))
    (hb : ∀ᶠ n in atTop, _root_.HilbertSchmidt.hsNormSq (A n) ≤ B) :
    _root_.HilbertSchmidt.hsNormSq K ≤ B := by
  have hB : 0 ≤ B := by
    obtain ⟨n, hn⟩ := hb.exists
    exact le_trans (_root_.HilbertSchmidt.hsNormSq_nonneg (A n)) hn
  have hwlp : Tendsto (fun n => (inner ℂ (⟨K, hK.memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2)
      (⟨A n, (hA n).memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2) : ℂ)) atTop
      (𝓝 ((inner ℂ (⟨K, hK.memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2)
        (⟨K, hK.memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2) : ℂ))) := by
    rw [← _root_.HilbertSchmidt.hsInner_eq_lp_inner hK hK]
    refine hw.congr fun n => ?_
    exact _root_.HilbertSchmidt.hsInner_eq_lp_inner hK (hA n)
  have hblp : ∀ᶠ n in atTop, ‖(⟨A n, (hA n).memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2)‖
      ≤ Real.sqrt B := by
    filter_upwards [hb] with n hn
    rw [show ‖(⟨A n, (hA n).memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2)‖
        = Real.sqrt (‖(⟨A n, (hA n).memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2)‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [_root_.HilbertSchmidt.lp_norm_sq (hA n)]
    exact hn
  have hnorm := norm_le_of_weak_limit_complex hwlp hblp
  rw [← _root_.HilbertSchmidt.lp_norm_sq hK]
  calc ‖(⟨K, hK.memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2)‖ ^ 2 ≤ (Real.sqrt B) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = B := Real.sq_sqrt hB

end GaloisForLFunctions.RHTower

end
