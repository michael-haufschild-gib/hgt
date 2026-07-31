import GaloisForLFunctions.HTGeometry.EllipticPoleSpace

/-!
# Principal jets of a meromorphic function at a pole

To bound the dimension of a space of lattice-periodic meromorphic functions with prescribed poles
one needs a *linear* handle on the principal part at each pole.  Multiplying by `(· − p)^d` clears a
pole of order at most `d`; the resulting function has a removable singularity, and its first `d`
Taylor coefficients at `p` are exactly the data of the principal part.

The removable singularity is taken canonically, by mathlib's normal-form operator
`toMeromorphicNFOn`, which agrees with the raw product off the poles and is analytic wherever the
order is nonnegative.  Linearity then follows from a general principle: two functions agreeing on a
*punctured* neighbourhood and continuous at the point agree on a full neighbourhood, hence have the
same jets.

* `eventuallyEq_nhds_of_nhdsNE_of_continuousAt` — the punctured-to-full upgrade;
* `poleClear` — the canonical analytic representative of `(· − p)^d · g` near `p`;
* `analyticAt_poleClear` — it is analytic at `p` once the cleared order is nonnegative;
* `principalJet` — its Taylor coefficients at `p`;
* **`principalJet_add`** and **`principalJet_smul`** — the jets depend linearly on `g`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-! ### Punctured agreement upgrades to full agreement -/

/-- **Two functions agreeing off a point and continuous at it agree near it.**  The missing value at
the point comes from uniqueness of limits; the upgrade to a full neighbourhood is mathlib's
`eventuallyEq_nhds_of_eventuallyEq_nhdsNE`. -/
theorem eventuallyEq_nhds_of_nhdsNE_of_continuousAt {f h : ℂ → ℂ} {x : ℂ}
    (heq : f =ᶠ[𝓝[≠] x] h) (hf : ContinuousAt f x) (hh : ContinuousAt h x) :
    f =ᶠ[𝓝 x] h := by
  refine eventuallyEq_nhds_of_eventuallyEq_nhdsNE heq ?_
  have h1 : Tendsto f (𝓝[≠] x) (𝓝 (f x)) := hf.continuousWithinAt.tendsto
  have h2 : Tendsto h (𝓝[≠] x) (𝓝 (h x)) := hh.continuousWithinAt.tendsto
  exact tendsto_nhds_unique (h1.congr' heq) h2

/-- Functions agreeing off a point and continuous at it have the same jets there. -/
theorem iteratedDeriv_congr_of_eventuallyEq_nhdsNE {f h : ℂ → ℂ} {x : ℂ} (k : ℕ)
    (heq : f =ᶠ[𝓝[≠] x] h) (hf : ContinuousAt f x) (hh : ContinuousAt h x) :
    iteratedDeriv k f x = iteratedDeriv k h x :=
  Filter.EventuallyEq.iteratedDeriv_eq k (eventuallyEq_nhds_of_nhdsNE_of_continuousAt heq hf hh)

/-! ### Clearing a pole -/

/-- The canonical analytic representative of `(· − p)^d · g` near `p`. -/
noncomputable def poleClear (g : ℂ → ℂ) (p : ℂ) (d : ℕ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun z => (z - p) ^ d * g z) Set.univ

/-- `poleClear` agrees with the raw product off the poles. -/
theorem poleClear_eventuallyEq_nhdsNE {g : ℂ → ℂ} {p : ℂ} {d : ℕ}
    (hg : MeromorphicOn (fun z => (z - p) ^ d * g z) Set.univ) (x : ℂ) :
    poleClear g p d =ᶠ[𝓝[≠] x] fun z => (z - p) ^ d * g z :=
  hg.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ x)

/-- **A cleared pole is analytic.**  If the order of `(· − p)^d · g` at `p` is nonnegative, the
canonical representative is analytic there. -/
theorem analyticAt_poleClear {g : ℂ → ℂ} {p : ℂ} {d : ℕ}
    (hg : MeromorphicOn (fun z => (z - p) ^ d * g z) Set.univ)
    (hord : 0 ≤ meromorphicOrderAt (fun z => (z - p) ^ d * g z) p) :
    AnalyticAt ℂ (poleClear g p d) p := by
  have hNF : MeromorphicNFOn (poleClear g p d) Set.univ :=
    meromorphicNFOn_toMeromorphicNFOn _ _
  refine (hNF (Set.mem_univ p)).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
  show 0 ≤ meromorphicOrderAt (toMeromorphicNFOn (fun z => (z - p) ^ d * g z) Set.univ) p
  rwa [meromorphicOrderAt_toMeromorphicNFOn hg (Set.mem_univ p)]

/-! ### The principal jets -/

/-- The Taylor coefficients at `p` of the cleared function: the data of the principal part. -/
noncomputable def principalJet (g : ℂ → ℂ) (p : ℂ) (d k : ℕ) : ℂ :=
  iteratedDeriv k (poleClear g p d) p

/-- **The principal jets are additive.** -/
theorem principalJet_add {g₁ g₂ : ℂ → ℂ} {p : ℂ} {d k : ℕ}
    (hg₁ : MeromorphicOn (fun z => (z - p) ^ d * g₁ z) Set.univ)
    (hg₂ : MeromorphicOn (fun z => (z - p) ^ d * g₂ z) Set.univ)
    (hgs : MeromorphicOn (fun z => (z - p) ^ d * (g₁ z + g₂ z)) Set.univ)
    (hord₁ : 0 ≤ meromorphicOrderAt (fun z => (z - p) ^ d * g₁ z) p)
    (hord₂ : 0 ≤ meromorphicOrderAt (fun z => (z - p) ^ d * g₂ z) p)
    (hords : 0 ≤ meromorphicOrderAt (fun z => (z - p) ^ d * (g₁ z + g₂ z)) p) :
    principalJet (fun z => g₁ z + g₂ z) p d k = principalJet g₁ p d k + principalJet g₂ p d k := by
  have ha₁ := analyticAt_poleClear hg₁ hord₁
  have ha₂ := analyticAt_poleClear hg₂ hord₂
  have has := analyticAt_poleClear hgs hords
  have heq : poleClear (fun z => g₁ z + g₂ z) p d
      =ᶠ[𝓝[≠] p] fun z => poleClear g₁ p d z + poleClear g₂ p d z := by
    filter_upwards [poleClear_eventuallyEq_nhdsNE hgs p, poleClear_eventuallyEq_nhdsNE hg₁ p,
      poleClear_eventuallyEq_nhdsNE hg₂ p] with z hz h₁ h₂
    rw [hz, h₁, h₂]
    ring
  have hcont : ContinuousAt (fun z => poleClear g₁ p d z + poleClear g₂ p d z) p :=
    (ha₁.continuousAt).add (ha₂.continuousAt)
  have hjet := iteratedDeriv_congr_of_eventuallyEq_nhdsNE k heq has.continuousAt hcont
  rw [principalJet, hjet, principalJet, principalJet]
  exact iteratedDeriv_add (ha₁.contDiffAt.of_le le_top) (ha₂.contDiffAt.of_le le_top)

/-- **The principal jets are homogeneous.** -/
theorem principalJet_smul {g : ℂ → ℂ} {p : ℂ} {d k : ℕ} (c : ℂ)
    (hg : MeromorphicOn (fun z => (z - p) ^ d * g z) Set.univ)
    (hgc : MeromorphicOn (fun z => (z - p) ^ d * (c * g z)) Set.univ)
    (hord : 0 ≤ meromorphicOrderAt (fun z => (z - p) ^ d * g z) p)
    (hordc : 0 ≤ meromorphicOrderAt (fun z => (z - p) ^ d * (c * g z)) p) :
    principalJet (fun z => c * g z) p d k = c * principalJet g p d k := by
  have ha := analyticAt_poleClear hg hord
  have hac := analyticAt_poleClear hgc hordc
  have heq : poleClear (fun z => c * g z) p d =ᶠ[𝓝[≠] p] fun z => c * poleClear g p d z := by
    filter_upwards [poleClear_eventuallyEq_nhdsNE hgc p, poleClear_eventuallyEq_nhdsNE hg p]
      with z hz h₁
    rw [hz, h₁]
    ring
  have hcont : ContinuousAt (fun z => c * poleClear g p d z) p :=
    continuousAt_const.mul ha.continuousAt
  have hjet := iteratedDeriv_congr_of_eventuallyEq_nhdsNE k heq hac.continuousAt hcont
  rw [principalJet, hjet, principalJet]
  exact iteratedDeriv_const_mul_field c (poleClear g p d)


/-! ### Finite linear combinations -/

/-- A finite sum of functions analytic at a point is analytic there, in applied form. -/
theorem analyticAt_finset_sum_apply {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (x : ℂ)
    (h : ∀ i ∈ s, AnalyticAt ℂ (F i) x) : AnalyticAt ℂ (fun z => ∑ i ∈ s, F i z) x := by
  have hsum := Finset.analyticAt_sum s h
  have hfun : (∑ i ∈ s, F i) = fun z => ∑ i ∈ s, F i z := by
    funext z; simp
  rwa [hfun] at hsum

/-- Jets of a finite sum of functions analytic at the point. -/
theorem iteratedDeriv_finset_sum_of_analyticAt {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ)
    (x : ℂ) (k : ℕ)
    (h : ∀ i ∈ s, AnalyticAt ℂ (F i) x) :
    iteratedDeriv k (fun z => ∑ i ∈ s, F i z) x = ∑ i ∈ s, iteratedDeriv k (F i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      have hA : AnalyticAt ℂ (F a) x := h a (Finset.mem_insert_self a t)
      have hT : ∀ i ∈ t, AnalyticAt ℂ (F i) x := fun i hi =>
        h i (Finset.mem_insert_of_mem hi)
      have hTsum : AnalyticAt ℂ (fun z => ∑ i ∈ t, F i z) x := analyticAt_finset_sum_apply t F x hT
      have hsplit : (fun z => ∑ i ∈ insert a t, F i z)
          = fun z => F a z + ∑ i ∈ t, F i z := by
        funext z
        rw [Finset.sum_insert ha]
      have hpi : (fun z => F a z + ∑ i ∈ t, F i z) = F a + fun z => ∑ i ∈ t, F i z := rfl
      rw [hsplit, hpi, iteratedDeriv_add (hA.contDiffAt.of_le le_top)
        (hTsum.contDiffAt.of_le le_top), ih hT, Finset.sum_insert ha]

/-- **The principal jets are linear in finite combinations.** -/
theorem principalJet_finset_sum {ι : Type*} (s : Finset ι) (g : ι → (ℂ → ℂ)) (c : ι → ℂ)
    {p : ℂ} {d k : ℕ}
    (hmer : ∀ i ∈ s, MeromorphicOn (fun z => (z - p) ^ d * g i z) Set.univ)
    (hord : ∀ i ∈ s, 0 ≤ meromorphicOrderAt (fun z => (z - p) ^ d * g i z) p)
    (hmerS : MeromorphicOn (fun z => (z - p) ^ d * ∑ i ∈ s, c i * g i z) Set.univ)
    (hordS : 0 ≤ meromorphicOrderAt (fun z => (z - p) ^ d * ∑ i ∈ s, c i * g i z) p) :
    principalJet (fun z => ∑ i ∈ s, c i * g i z) p d k
      = ∑ i ∈ s, c i * principalJet (g i) p d k := by
  classical
  have hAi : ∀ i ∈ s, AnalyticAt ℂ (poleClear (g i) p d) p := fun i hi =>
    analyticAt_poleClear (hmer i hi) (hord i hi)
  have hAS : AnalyticAt ℂ (poleClear (fun z => ∑ i ∈ s, c i * g i z) p d) p :=
    analyticAt_poleClear hmerS hordS
  have hAcomb : AnalyticAt ℂ (fun z => ∑ i ∈ s, c i * poleClear (g i) p d z) p :=
    analyticAt_finset_sum_apply s (fun i z => c i * poleClear (g i) p d z) p
      (fun i hi => analyticAt_const.mul (hAi i hi))
  have hall : ∀ᶠ z in 𝓝[≠] p, ∀ i ∈ s, poleClear (g i) p d z = (z - p) ^ d * g i z := by
    rw [Finset.eventually_all]
    exact fun i hi => poleClear_eventuallyEq_nhdsNE (hmer i hi) p
  have heq : poleClear (fun z => ∑ i ∈ s, c i * g i z) p d
      =ᶠ[𝓝[≠] p] fun z => ∑ i ∈ s, c i * poleClear (g i) p d z := by
    filter_upwards [poleClear_eventuallyEq_nhdsNE hmerS p, hall] with z hz hi
    rw [hz, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i his => ?_)
    rw [hi i his]
    ring
  have hjet := iteratedDeriv_congr_of_eventuallyEq_nhdsNE k heq hAS.continuousAt
    hAcomb.continuousAt
  rw [principalJet, hjet,
    iteratedDeriv_finset_sum_of_analyticAt s (fun i z => c i * poleClear (g i) p d z) p k
      (fun i hi => analyticAt_const.mul (hAi i hi))]
  exact Finset.sum_congr rfl (fun i _ => iteratedDeriv_const_mul_field (c i) (poleClear (g i) p d))

end GaloisForLFunctions.HTGeometry
