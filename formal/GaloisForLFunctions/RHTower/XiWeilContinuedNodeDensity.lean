import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity
import GaloisForLFunctions.RHTower.XiQuotientRealDecay

/-!
# Density of the continued-domain Cauchy nodes

The prime-plus-Gamma trace represents the Cauchy polarization only for nodes in the domain where
the continued relative trace is defined.  This file shows that the restriction costs nothing.

Every element of a node-restricted Cauchy span is the evaluation vector of a finite Cauchy packet
with nodes in the same set, and the annihilator of the restricted span is again the fibrewise
mean-zero space as soon as the nodes accumulate at every Xi zero.  The continued domain does
accumulate at every Xi zero, because its two open conditions hold at the zero itself and the
vanishing of zeta fails only at the zero.  Consequently the evaluation vector of an arbitrary
square-summable test function is a limit of such packets, and the zero-side Weil polarization
against a fixed Cauchy packet is approximated to any accuracy by a finite continued
prime-plus-Gamma double sum.
-/

open Complex Metric Set Filter Topology

namespace RHTower

noncomputable section


/-- The span of the regular Cauchy evaluation vectors whose nodes lie in a prescribed set. -/
def xiWeilCauchyNodeSpan (N : Set ℂ) : Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  Submodule.span ℂ {v | ∃ z : XiCRegularPoint, (z : ℂ) ∈ N ∧ v = xiWeilCauchyLp z}

theorem xiWeilEvaluationLp_add (F G : ℂ → ℂ) (hF : XiWeilSquareSummable F)
    (hG : XiWeilSquareSummable G) (hFG : XiWeilSquareSummable (F + G)) :
    xiWeilEvaluationLp (F + G) hFG = xiWeilEvaluationLp F hF + xiWeilEvaluationLp G hG := by
  apply Subtype.ext
  funext q
  rfl

theorem xiWeilEvaluationLp_congr {F G : ℂ → ℂ} (hF : XiWeilSquareSummable F)
    (hG : XiWeilSquareSummable G) (h : F = G) :
    xiWeilEvaluationLp F hF = xiWeilEvaluationLp G hG := by
  subst h; rfl

/-- Every element of the Cauchy node span is the evaluation vector of a finite Cauchy packet with
nodes in the same set: the packets are closed under sums (take the union of the node sets and
extend the coefficients by zero) and under scalars. -/
theorem exists_cauchyPacket_of_mem_xiWeilCauchyNodeSpan {N : Set ℂ}
    {x : lp (fun _ : XiZeroCopy => ℂ) 2} (hx : x ∈ xiWeilCauchyNodeSpan N) :
    ∃ (s : Finset ℂ) (c : ℂ → ℂ) (hreg : ∀ z ∈ s, XiC z ≠ 0), (∀ z ∈ s, z ∈ N) ∧
      x = xiWeilEvaluationLp (xiWeilCauchyPacket s c)
        (XiWeilSquareSummable_cauchyPacket c hreg) := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨z, hzN, rfl⟩ := hy
      refine ⟨{(z : ℂ)}, fun _ => 1, ?_, ?_, ?_⟩
      · intro w hw
        rw [Finset.mem_singleton] at hw
        exact hw ▸ z.2
      · intro w hw
        rw [Finset.mem_singleton] at hw
        exact hw ▸ hzN
      · apply Subtype.ext
        funext q
        simp [xiWeilCauchyPacket, xiWeilCauchyLp, xiWeilEvaluationLp]
  | zero =>
      refine ⟨∅, 0, by simp, by simp, ?_⟩
      apply Subtype.ext
      funext q
      simp [xiWeilCauchyPacket, xiWeilEvaluationLp]
  | add y w hy hw ihy ihw =>
      obtain ⟨s, c, hregs, hsN, rfl⟩ := ihy
      obtain ⟨t, d, hregt, htN, rfl⟩ := ihw
      refine ⟨s ∪ t, (fun z => if z ∈ s then c z else 0) + (fun z => if z ∈ t then d z else 0),
        ?_, ?_, ?_⟩
      · intro z hz
        rcases Finset.mem_union.mp hz with h | h
        · exact hregs z h
        · exact hregt z h
      · intro z hz
        rcases Finset.mem_union.mp hz with h | h
        · exact hsN z h
        · exact htN z h
      · rw [← xiWeilEvaluationLp_add _ _ (XiWeilSquareSummable_cauchyPacket c hregs)
          (XiWeilSquareSummable_cauchyPacket d hregt)]
        refine xiWeilEvaluationLp_congr _ _ ?_
        funext a
        simp only [xiWeilCauchyPacket, Pi.add_apply, Finset.sum_add_distrib, add_mul,
          Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.sum_subset (Finset.subset_union_left (s₁ := s) (s₂ := t))
            (fun z _ hz => by rw [if_neg hz, zero_mul])]
          exact Finset.sum_congr rfl (fun z hz => by rw [if_pos hz])
        · rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := s) (s₂ := t))
            (fun z _ hz => by rw [if_neg hz, zero_mul])]
          exact Finset.sum_congr rfl (fun z hz => by rw [if_pos hz])
        exact (XiWeilSquareSummable_cauchyPacket c hregs).add
          (XiWeilSquareSummable_cauchyPacket d hregt)
  | smul a y hy ih =>
      obtain ⟨s, c, hregs, hsN, rfl⟩ := ih
      refine ⟨s, fun z => a * c z, hregs, hsN, ?_⟩
      apply Subtype.ext
      funext q
      simp only [lp.coeFn_smul, Pi.smul_apply, xiWeilEvaluationLp, xiWeilCauchyPacket,
        smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun z _ => by ring)


/-- The node domain on which the continued prime-plus-Gamma trace computes the Cauchy
polarization. -/
def xiWeilContinuedNodeSet : Set ℂ :=
  {z | 0 < (1 / 2 + z * I).re ∧ 1 / 2 + z * I ≠ 1 ∧ riemannZeta (1 / 2 + z * I) ≠ 0}

theorem half_add_xiSpectralPointSupport_mul_I (ρ : XiDivisorSupport) :
    1 / 2 + xiSpectralPointSupport ρ * I = (ρ : ℂ) := by
  rw [xiSpectralPointSupport]
  have hI : (-I : ℂ) * I = 1 := by
    rw [neg_mul, Complex.I_mul_I]
    ring
  calc 1 / 2 + ((ρ : ℂ) - 1 / 2) * (-I) * I
      = 1 / 2 + ((ρ : ℂ) - 1 / 2) * ((-I) * I) := by ring
    _ = (ρ : ℂ) := by rw [hI]; ring

/-- Every Xi zero is approached from inside the continued node domain: the domain conditions are
open and hold at the zero itself except for the vanishing of zeta, which fails only at the zero. -/
theorem eventually_mem_xiWeilContinuedNodeSet (ρ : XiDivisorSupport) (E : Finset ℂ) :
    ∀ᶠ z in nhdsWithin (xiSpectralPointSupport ρ) {xiSpectralPointSupport ρ}ᶜ,
      z ∈ xiWeilContinuedNodeSet \ (E : Set ℂ) := by
  classical
  set a : ℂ := xiSpectralPointSupport ρ with ha
  have hval : 1 / 2 + a * I = (ρ : ℂ) := half_add_xiSpectralPointSupport_mul_I ρ
  have hstrip := xi_divisor_support_re_mem_open_unit ρ
  have hg : Continuous (fun z : ℂ => 1 / 2 + z * I) := by fun_prop
  have h1 : ∀ᶠ z in nhds a, 0 < (1 / 2 + z * I).re := by
    have hopen : IsOpen {z : ℂ | 0 < (1 / 2 + z * I).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp hg)
    exact hopen.eventually_mem (by simpa only [Set.mem_setOf_eq, hval] using hstrip.1)
  have h2 : ∀ᶠ z in nhds a, 1 / 2 + z * I ≠ 1 := by
    refine (hg.tendsto a).eventually (eventually_ne_nhds ?_)
    rw [hval]
    intro hcon
    rw [hcon] at hstrip
    simp at hstrip
  have h3 : ∀ᶠ z in nhdsWithin a {a}ᶜ, XiC z ≠ 0 := eventually_XiC_ne_zero_punctured a
  have h4 : ∀ᶠ z in nhdsWithin a {a}ᶜ, z ∉ (E : Set ℂ) := by
    have hclosed : IsClosed ((E : Set ℂ) \ {a}) :=
      (E.finite_toSet.subset Set.sdiff_subset).isClosed
    have hmem : a ∉ ((E : Set ℂ) \ {a}) := by simp
    have hev : ∀ᶠ z in nhds a, z ∉ ((E : Set ℂ) \ {a}) :=
      hclosed.isOpen_compl.eventually_mem hmem
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hza
    intro hzE
    exact hz ⟨hzE, hza⟩
  filter_upwards [h1.filter_mono nhdsWithin_le_nhds, h2.filter_mono nhdsWithin_le_nhds, h3, h4]
    with z hz1 hz2 hz3 hz4
  refine ⟨⟨hz1, hz2, ?_⟩, hz4⟩
  intro hzeta
  exact hz3 ((xi_eq_zero_iff hz1 hz2).mpr hzeta)

/-- The annihilator of a node-restricted Cauchy span is again the fibrewise mean-zero space, as
soon as the nodes accumulate at every Xi zero. -/
theorem mem_orthogonal_xiWeilCauchyNodeSpan_iff {N : Set ℂ}
    (hN : ∀ ρ : XiDivisorSupport,
      ∀ᶠ z in nhdsWithin (xiSpectralPointSupport ρ) {xiSpectralPointSupport ρ}ᶜ, z ∈ N)
    (u : lp (fun _ : XiZeroCopy => ℂ) 2) :
    u ∈ (xiWeilCauchyNodeSpan N)ᗮ ↔
      ∀ ρ : XiDivisorSupport, xiWeilFiberSum (fun q => u q) ρ = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro hx
    refine xiWeilFiberSum_eq_zero_of_inner_xiWeilCauchyLp_eq_zero_on_nodes u hN (fun z hzN => ?_)
    exact hx _ (Submodule.subset_span ⟨z, hzN, rfl⟩)
  · intro hfib x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨z, _, rfl⟩ := hy
        exact inner_xiWeilCauchyLp_eq_zero_of_xiWeilFiberSum_eq_zero u hfib z
    | zero => simp
    | add y w hy hw ihy ihw => rw [inner_add_left, ihy, ihw, add_zero]
    | smul c y hy ih => rw [inner_smul_left, ih, mul_zero]

/-- **Every evaluation vector is a limit of Cauchy packets with nodes in the continued domain.**
Restricting the nodes to the domain where the prime-plus-Gamma trace is defined costs nothing: the
restricted span has the same annihilator, hence the same closure. -/
theorem xiWeilEvaluationLp_mem_closure_xiWeilCauchyNodeSpan
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) (E : Finset ℂ) :
    xiWeilEvaluationLp F hF ∈
      (xiWeilCauchyNodeSpan (xiWeilContinuedNodeSet \ (E : Set ℂ))).topologicalClosure := by
  have hN : ∀ ρ : XiDivisorSupport,
      ∀ᶠ z in nhdsWithin (xiSpectralPointSupport ρ) {xiSpectralPointSupport ρ}ᶜ,
        z ∈ xiWeilContinuedNodeSet \ (E : Set ℂ) :=
    fun ρ => eventually_mem_xiWeilContinuedNodeSet ρ E
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
  intro u hu
  have hfib := (mem_orthogonal_xiWeilCauchyNodeSpan_iff hN u).mp hu
  have h0 := inner_xiWeilEvaluationLp_eq_zero_of_xiWeilFiberSum_eq_zero F hF u hfib
  rw [← inner_conj_symm, h0, map_zero]

/-- **Explicit-formula approximation beyond the resolvent core.**  For an arbitrary square-summable
test function the zero-side Weil polarization against a fixed Cauchy packet is approximated, to any
accuracy, by a finite continued prime-plus-Gamma double sum.  The nodes are chosen in the continued
domain and away from the conjugated nodes of the fixed packet, which is possible because the
restricted Cauchy span is still dense in the range of the evaluation map. -/
theorem exists_cauchyPacket_continuedPrimeArchSource_approx
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F)
    {t : Finset ℂ} {d : ℂ → ℂ}
    (hwpos : ∀ w ∈ t, 0 < (1 / 2 + (starRingEnd ℂ) w * I).re)
    (hw1 : ∀ w ∈ t, 1 / 2 + (starRingEnd ℂ) w * I ≠ 1)
    (hwzeta : ∀ w ∈ t, riemannZeta (1 / 2 + (starRingEnd ℂ) w * I) ≠ 0)
    (hwreg : ∀ w ∈ t, XiC w ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℂ) (c : ℂ → ℂ),
      (∀ z ∈ s, 0 < (1 / 2 + z * I).re ∧ 1 / 2 + z * I ≠ 1 ∧
        riemannZeta (1 / 2 + z * I) ≠ 0) ∧
      ‖(∑ z ∈ s, ∑ w ∈ t,
          c z * (starRingEnd ℂ) (d w) *
            ((continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) w) -
              continuedPrimeArchSourceRelativeTrace z) / (z - (starRingEnd ℂ) w))) -
        xiWeilPolarization F (xiWeilCauchyPacket t d)‖ ≤ ε := by
  classical
  set E : Finset ℂ := t.image (starRingEnd ℂ) with hE
  have hG : XiWeilSquareSummable (xiWeilCauchyPacket t d) :=
    XiWeilSquareSummable_cauchyPacket d hwreg
  set K : ℝ := ‖xiWeilEvaluationLp (xiWeilCauchyPacket t d) hG‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  have hmem0 := xiWeilEvaluationLp_mem_closure_xiWeilCauchyNodeSpan F hF E
  have hmem : xiWeilEvaluationLp F hF ∈
      closure ((xiWeilCauchyNodeSpan (xiWeilContinuedNodeSet \ (E : Set ℂ)) :
        Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2)) : Set (lp (fun _ : XiZeroCopy => ℂ) 2)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hmem0
  rw [Metric.mem_closure_iff] at hmem
  obtain ⟨y, hy, hdist⟩ := hmem (ε / (K + 1)) (by positivity)
  obtain ⟨s, c, hreg, hsN, hrepr⟩ := exists_cauchyPacket_of_mem_xiWeilCauchyNodeSpan hy
  refine ⟨s, c, fun z hz => (hsN z hz).1, ?_⟩
  have hsep : ∀ z ∈ s, ∀ w ∈ t, z ≠ (starRingEnd ℂ) w := by
    intro z hz w hw hcon
    exact (hsN z hz).2 (by rw [hE, Finset.coe_image]; exact ⟨w, hw, hcon.symm⟩)
  rw [← xiWeilPolarization_cauchyPacket_eq_continuedPrimeArchSource
    (fun z hz => (hsN z hz).1.1) (fun z hz => (hsN z hz).1.2.1) (fun z hz => (hsN z hz).1.2.2)
    hwpos hw1 hwzeta hsep]
  have hlip := norm_xiWeilPolarization_sub_left_le
    (XiWeilSquareSummable_cauchyPacket c hreg) hF hG
  refine le_trans hlip ?_
  have hnormle : ‖xiWeilEvaluationLp (xiWeilCauchyPacket s c)
      (XiWeilSquareSummable_cauchyPacket c hreg) - xiWeilEvaluationLp F hF‖ ≤ ε / (K + 1) := by
    rw [← hrepr, ← dist_eq_norm, dist_comm]
    exact hdist.le
  calc ‖xiWeilEvaluationLp (xiWeilCauchyPacket s c)
        (XiWeilSquareSummable_cauchyPacket c hreg) - xiWeilEvaluationLp F hF‖ * K
      ≤ (ε / (K + 1)) * K := by gcongr
    _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

end

end RHTower
