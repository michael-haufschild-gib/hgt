import GaloisForLFunctions.MultipleEllipticGammaLogConvergence

/-!
# The convergent all-order multiple elliptic-gamma hierarchy

Finite coordinate telescoping is passed to the absolutely convergent all-order kernel.  In every
nome direction, the kernel difference is exactly the lower-order kernel on the coordinate-deletion
face.  No hierarchy equation is assumed.
-/

open Complex Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem multipleEllipticGammaForwardArgument_tendsto_zero_coordinate
    {p : ι → ℂ} {x : ℂ} (q : ι) (m : {i : ι // i ≠ q} → ℕ)
    (hpq : ‖p q‖ < 1) :
    Tendsto (fun N => multipleEllipticGammaForwardArgument p x
      (multipleEllipticGammaMergeIndex q N m)) atTop (nhds 0) := by
  let C : ℂ := ∏ i : {i : ι // i ≠ q}, p i ^ (m i + 1)
  have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hpq
  have ht := ((hpow.mul_const (p q)).mul_const C).div_const x
  convert ht using 1
  · funext N
    rw [multipleEllipticGammaForwardArgument,
      Fintype.prod_eq_mul_prod_subtype_ne
        (fun i => p i ^ (multipleEllipticGammaMergeIndex q N m i + 1)) q]
    simp only [multipleEllipticGammaMergeIndex_self,
      multipleEllipticGammaMergeIndex_ne]
    dsimp [C]
    rw [pow_succ]
  · simp

theorem multipleEllipticGammaBackwardArgument_tendsto_zero_coordinate
    {p : ι → ℂ} {x : ℂ} (q : ι) (m : {i : ι // i ≠ q} → ℕ)
    (hpq : ‖p q‖ < 1) :
    Tendsto (fun N => multipleEllipticGammaBackwardArgument p x
      (multipleEllipticGammaMergeIndex q (N + 1) m)) atTop (nhds 0) := by
  let C : ℂ := ∏ i : {i : ι // i ≠ q}, p i ^ m i
  have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hpq
  have ht := ((hpow.mul_const (p q)).mul_const C).mul_const x
  convert ht using 1
  · funext N
    rw [multipleEllipticGammaBackwardArgument,
      Fintype.prod_eq_mul_prod_subtype_ne
        (fun i => p i ^ multipleEllipticGammaMergeIndex q (N + 1) m i) q]
    simp only [multipleEllipticGammaMergeIndex_self,
      multipleEllipticGammaMergeIndex_ne]
    dsimp [C]
    rw [pow_succ]
  · simp

/-- Both terminal tails in one coordinate fiber tend to zero. -/
theorem multipleEllipticGammaLogTerminalTails_tendsto_zero_coordinate
    {p : ι → ℂ} {x : ℂ} (q : ι) (m : {i : ι // i ≠ q} → ℕ)
    (hpq : ‖p q‖ < 1) :
    Tendsto (fun N =>
      -ellipticGammaLogAtom (multipleEllipticGammaForwardArgument p x
        (multipleEllipticGammaMergeIndex q N m)) +
      multipleEllipticGammaLogSign ι *
        ellipticGammaLogAtom (multipleEllipticGammaBackwardArgument p x
          (multipleEllipticGammaMergeIndex q (N + 1) m))) atTop (nhds 0) := by
  have hf := ellipticGammaLogAtom_tendsto_zero.comp
    (multipleEllipticGammaForwardArgument_tendsto_zero_coordinate
      (x := x) q m hpq)
  have hb := ellipticGammaLogAtom_tendsto_zero.comp
    (multipleEllipticGammaBackwardArgument_tendsto_zero_coordinate
      (x := x) q m hpq)
  simpa using hf.neg.add (hb.const_mul (multipleEllipticGammaLogSign ι))

/-- Infinite telescoping in one coordinate fiber. -/
theorem multipleEllipticGammaLogSummand_tsum_mul_coordinate_fiber
    {p : ι → ℂ} {x : ℂ} (q : ι) (m : {i : ι // i ≠ q} → ℕ)
    (hp0 : ∀ i, p i ≠ 0) (hp : ∀ i, ‖p i‖ < 1) (hx : x ≠ 0) :
    (∑' k : ℕ, multipleEllipticGammaLogSummand p (p q * x)
        (multipleEllipticGammaMergeIndex q k m)) -
      ∑' k : ℕ, multipleEllipticGammaLogSummand p x
        (multipleEllipticGammaMergeIndex q k m) =
      multipleEllipticGammaLogSummand
        (fun i : {i : ι // i ≠ q} => p i) x m := by
  let e := multipleEllipticGammaSplitIndex q
  have hmulGlobal := summable_multipleEllipticGammaLogSummand
    (p := p) (x := p q * x) hp
  have hbaseGlobal := summable_multipleEllipticGammaLogSummand
    (p := p) (x := x) hp
  have hmulProd : Summable (fun km : ℕ × ({i : ι // i ≠ q} → ℕ) =>
      multipleEllipticGammaLogSummand p (p q * x)
        (multipleEllipticGammaMergeIndex q km.1 km.2)) := by
    simpa [e] using ((e.symm.summable_iff).2 hmulGlobal)
  have hbaseProd : Summable (fun km : ℕ × ({i : ι // i ≠ q} → ℕ) =>
      multipleEllipticGammaLogSummand p x
        (multipleEllipticGammaMergeIndex q km.1 km.2)) := by
    simpa [e] using ((e.symm.summable_iff).2 hbaseGlobal)
  have hmul := hmulProd.prod_symm.prod_factor m
  have hbase := hbaseProd.prod_symm.prod_factor m
  have hL : Tendsto
      (fun N =>
        (∑ k ∈ Finset.range (N + 1),
          multipleEllipticGammaLogSummand p (p q * x)
            (multipleEllipticGammaMergeIndex q k m)) -
        ∑ k ∈ Finset.range (N + 1),
          multipleEllipticGammaLogSummand p x
            (multipleEllipticGammaMergeIndex q k m))
      atTop
      (nhds ((∑' k : ℕ, multipleEllipticGammaLogSummand p (p q * x)
          (multipleEllipticGammaMergeIndex q k m)) -
        ∑' k : ℕ, multipleEllipticGammaLogSummand p x
          (multipleEllipticGammaMergeIndex q k m))) := by
    apply Tendsto.sub
    · simpa only using hmul.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    · simpa only using hbase.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hR : Tendsto
      (fun N => multipleEllipticGammaLogSummand
          (fun i : {i : ι // i ≠ q} => p i) x m +
        (-ellipticGammaLogAtom (multipleEllipticGammaForwardArgument p x
            (multipleEllipticGammaMergeIndex q N m)) +
          multipleEllipticGammaLogSign ι *
            ellipticGammaLogAtom (multipleEllipticGammaBackwardArgument p x
              (multipleEllipticGammaMergeIndex q (N + 1) m))))
      atTop
      (nhds (multipleEllipticGammaLogSummand
        (fun i : {i : ι // i ≠ q} => p i) x m)) := by
    simpa using tendsto_const_nhds.add
      (multipleEllipticGammaLogTerminalTails_tendsto_zero_coordinate q m (hp q))
  apply tendsto_nhds_unique hL
  apply hR.congr'
  filter_upwards with N
  rw [multipleEllipticGammaLogSummand_sum_mul_coordinate p x q m (hp0 q) hx]
  ring

/-- Fubini decomposition into fibers of any chosen coordinate. -/
theorem multipleEllipticGammaLogKernel_eq_tsum_coordinate_fibers
    {p : ι → ℂ} {x : ℂ} (q : ι) (hp : ∀ i, ‖p i‖ < 1) :
    multipleEllipticGammaLogKernel p x =
      ∑' m : {i : ι // i ≠ q} → ℕ, ∑' k : ℕ,
        multipleEllipticGammaLogSummand p x
          (multipleEllipticGammaMergeIndex q k m) := by
  let e : (({i : ι // i ≠ q} → ℕ) × ℕ) ≃ (ι → ℕ) :=
    (Equiv.prodComm _ _).trans (multipleEllipticGammaSplitIndex q).symm
  have hglobal := summable_multipleEllipticGammaLogSummand (p := p) (x := x) hp
  have hprod : Summable (fun mk : ({i : ι // i ≠ q} → ℕ) × ℕ =>
      multipleEllipticGammaLogSummand p x
        (multipleEllipticGammaMergeIndex q mk.2 mk.1)) := by
    simpa [e] using ((e.summable_iff).2 hglobal)
  rw [multipleEllipticGammaLogKernel]
  rw [← e.tsum_eq (multipleEllipticGammaLogSummand p x)]
  simpa [e] using hprod.tsum_prod

/-- **Constructed all-order hierarchy equation.** Multiplication of the elliptic variable by any
chosen nome lowers the order by deleting exactly that nome coordinate. -/
theorem multipleEllipticGammaLogKernel_mul_coordinate_sub
    {p : ι → ℂ} {x : ℂ} (q : ι)
    (hp0 : ∀ i, p i ≠ 0) (hp : ∀ i, ‖p i‖ < 1) (hx : x ≠ 0) :
    multipleEllipticGammaLogKernel p (p q * x) -
        multipleEllipticGammaLogKernel p x =
      multipleEllipticGammaLogKernel
        (fun i : {i : ι // i ≠ q} => p i) x := by
  rw [multipleEllipticGammaLogKernel_eq_tsum_coordinate_fibers q hp,
    multipleEllipticGammaLogKernel_eq_tsum_coordinate_fibers q hp,
    multipleEllipticGammaLogKernel]
  have hmulGlobal := summable_multipleEllipticGammaLogSummand
    (p := p) (x := p q * x) hp
  have hbaseGlobal := summable_multipleEllipticGammaLogSummand
    (p := p) (x := x) hp
  let e : (({i : ι // i ≠ q} → ℕ) × ℕ) ≃ (ι → ℕ) :=
    (Equiv.prodComm _ _).trans (multipleEllipticGammaSplitIndex q).symm
  have hmulProd : Summable (fun mk : ({i : ι // i ≠ q} → ℕ) × ℕ =>
      multipleEllipticGammaLogSummand p (p q * x)
        (multipleEllipticGammaMergeIndex q mk.2 mk.1)) := by
    simpa [e] using ((e.summable_iff).2 hmulGlobal)
  have hbaseProd : Summable (fun mk : ({i : ι // i ≠ q} → ℕ) × ℕ =>
      multipleEllipticGammaLogSummand p x
        (multipleEllipticGammaMergeIndex q mk.2 mk.1)) := by
    simpa [e] using ((e.summable_iff).2 hbaseGlobal)
  rw [← hmulProd.prod.tsum_sub hbaseProd.prod]
  apply tsum_congr
  intro m
  exact multipleEllipticGammaLogSummand_tsum_mul_coordinate_fiber
    q m hp0 hp hx

end

end GaloisForLFunctions
