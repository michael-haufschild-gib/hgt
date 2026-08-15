import GaloisForLFunctions.RHTower.CCMTwoChannelGraph

/-!
# Real spectral factors have zero transverse logarithmic graph

Three exact mechanisms of the card are formalized.

*The rank-one pole coordinate.*  The Cauchy insertion splits exactly into a causal difference
quotient and one anti-causal rank-one term, which is `(7)`; that term is a **nonzero** function
whenever the residue is nonzero.

*Distinct pole coordinates cannot cancel.*  A finite combination of Cauchy kernels with distinct
non-real poles that vanishes on the whole real line has all coefficients zero.  This is the step
that upgrades "one nonzero evaluation coordinate per off-line zero" to "the operator is nonzero".

*The graph-core shortcut absorbs the conclusion.*  If every finite stage is the zero operator and
the stages converge, the limit is zero; and if every compression of a vector vanishes while the
compressions converge back to it, the vector is zero.  Together these are the deduction
`(8)` + `(9)` ⟹ `D_Ξ = 0` of section 3.

The Smirnov maximum principle, the Hardy characterization of zero Hankel symbols, the Cartwright
class and the analytic construction of `D_Ξ` are cited parents and stay outside the Lean statement.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The rank-one pole coordinate -/

/-- **Equation (7), nonvanishing.**  The anti-causal rank-one coordinate attached to an upper
half-plane pole is a nonzero function of the real variable. -/
theorem antiCausal_coordinate_ne_zero {c : ℂ} {w : ℂ} (hc : c ≠ 0) (hw : 0 < w.im) :
    (fun x : ℝ => c / ((x : ℂ) - w)) ≠ 0 := by
  intro hzero
  have h0 : c / ((0 : ℂ) - w) = 0 := by
    have := congrFun hzero 0
    simpa using this
  have hne : ((0 : ℂ) - w) ≠ 0 := by
    intro hcon
    have : w = 0 := by linear_combination -hcon
    rw [this] at hw
    simp at hw
  exact hc ((div_eq_zero_iff.mp h0).resolve_right hne)

/-! ## Distinct pole coordinates cannot cancel -/

/-- **Section 2, independence step.**  A finite combination of Cauchy kernels with distinct non-real
poles vanishing on the whole real line has all coefficients zero. -/
theorem cauchy_coeff_eq_zero_of_vanishing_on_real {n : ℕ} {w : Fin n → ℂ} {c : Fin n → ℂ}
    (hw : Function.Injective w) (hnr : ∀ (i : Fin n) (x : ℝ), (x : ℂ) ≠ w i)
    (h : ∀ x : ℝ, ∑ i, c i / ((x : ℂ) - w i) = 0) (k : Fin n) : c k = 0 := by
  classical
  set P : Polynomial ℂ :=
    ∑ i, Polynomial.C (c i) * ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (w j))
    with hPdef
  have hevalP : ∀ z : ℂ,
      P.eval z = ∑ i, c i * ∏ j ∈ Finset.univ.erase i, (z - w j) := by
    intro z
    rw [hPdef]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]
  have hroot : ∀ x : ℝ, P.eval (x : ℂ) = 0 := by
    intro x
    have hne : ∀ i, ((x : ℂ) - w i) ≠ 0 := fun i => sub_ne_zero.mpr (hnr i x)
    have hmul : (∑ i, c i / ((x : ℂ) - w i)) * ∏ j, ((x : ℂ) - w j)
        = ∑ i, c i * ∏ j ∈ Finset.univ.erase i, ((x : ℂ) - w j) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
        mul_comm (∏ j ∈ Finset.univ.erase i, ((x : ℂ) - w j)) ((x : ℂ) - w i),
        ← mul_assoc, div_mul_cancel₀ _ (hne i)]
    rw [hevalP, ← hmul, h x, zero_mul]
  have hPzero : P = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot P ?_
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective Complex.ofReal_injective)
    rintro z ⟨x, rfl⟩
    exact hroot x
  have hk : P.eval (w k) = c k * ∏ j ∈ Finset.univ.erase k, (w k - w j) := by
    rw [hevalP]
    refine Finset.sum_eq_single k ?_ (fun hcon => absurd (Finset.mem_univ k) hcon)
    intro i _ hik
    have hmem : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ k⟩
    have : ∏ j ∈ Finset.univ.erase i, (w k - w j) = 0 :=
      Finset.prod_eq_zero hmem (by ring)
    rw [this, mul_zero]
  have hprod : (∏ j ∈ Finset.univ.erase k, (w k - w j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    exact sub_ne_zero.mpr fun hcon => hjk (hw hcon.symm)
  rw [hPzero, Polynomial.eval_zero] at hk
  exact (mul_eq_zero.mp hk.symm).resolve_right hprod

/-! ## The graph-core shortcut absorbs the conclusion -/

/-- **Equations (8)–(9).**  A convergent family of zero operators has zero limit. -/
theorem eq_zero_of_tendsto_of_forall_eq_zero {α β : Type*} [TopologicalSpace β] [T2Space β]
    [Zero β] {l : Filter α} [l.NeBot] {F : α → β} {g : β}
    (hzero : ∀ a, F a = 0) (hconv : Tendsto F l (nhds g)) : g = 0 := by
  have hz : Tendsto F l (nhds 0) := by
    refine tendsto_const_nhds.congr fun a => (hzero a).symm
  exact tendsto_nhds_unique hconv hz

/-- **Section 3, compression step.**  If every compression of a vector vanishes while the
compressions converge back to it, the vector is zero. -/
theorem eq_zero_of_forall_compression_zero {β : Type*} [TopologicalSpace β] [T2Space β]
    [Zero β] {l : Filter ℝ} [l.NeBot] {Q : ℝ → β} {x : β}
    (hQ : ∀ u, Q u = 0) (hconv : Tendsto Q l (nhds x)) : x = 0 :=
  eq_zero_of_tendsto_of_forall_eq_zero hQ hconv

end GaloisForLFunctions.RHTower

end
