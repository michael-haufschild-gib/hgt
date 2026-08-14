import GaloisForLFunctions.HTGeometry.DescPochhammerProductBasis
import GaloisForLFunctions.HTGeometry.MultiNodeInjectiveParameter

/-!
# Slot sequences are separated by the square-free key identity

A jet monomial of a family of dilated sources presents itself, once its jet-exponent profile is
flattened, as a *slot sequence*: a tuple `w : Fin D → ι × ℕ` recording for each slot the dilation
it carries and the jet order it consumes.  At a square-free key `k` the contribution of a slot
sequence is

```text
(∏_s desc_{(w s).2}(k_s)) · ∏_s q_{(w s).1}^{k_s} ,
```

an exponential polynomial whose node tuple is the dilation part of `w` and whose polynomial part is
the product of falling factorials of the jet orders.  Two separations then apply in turn: distinct
dilation tuples are separated by the multi-node theorem, and distinct jet-order tuples by the
linear independence of the falling-factorial products.  Together they show that a vanishing family
of such contributions has all coefficients zero — the separation no growth argument can perform,
because all translates of one source share a magnitude profile.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [DecidableEq ι] {D : ℕ}

/-- The dilation tuple of a slot sequence. -/
def slotNode (w : Fin D → ι × ℕ) : Fin D → ι := fun s => (w s).1

/-- The jet-order tuple of a slot sequence. -/
def slotOrder (w : Fin D → ι × ℕ) : Fin D → ℕ := fun s => (w s).2

omit [DecidableEq ι] in
theorem slotSeq_ext {w w' : Fin D → ι × ℕ} (h1 : slotNode w = slotNode w')
    (h2 : slotOrder w = slotOrder w') : w = w' := by
  funext s
  refine Prod.ext ?_ ?_
  · exact congrFun h1 s
  · exact congrFun h2 s

/-- The contribution of one slot sequence at a key. -/
noncomputable def slotTerm (q : ι → ℂ) (w : Fin D → ι × ℕ) (k : Fin D → ℕ) : ℂ :=
  (∏ s, (((k s).descFactorial ((w s).2) : ℕ) : ℂ)) * ∏ s, (q (w s).1) ^ (k s)

/-- **Slot sequences are separated.**  A family of slot-sequence contributions vanishing at every
injective key above the jet order has all its coefficients zero. -/
theorem slotSequence_coeff_eq_zero (q : ι → ℂ) (hq0 : ∀ i, q i ≠ 0)
    (hqinj : Function.Injective q) (n : ℕ)
    (T : Finset (Fin D → ι × ℕ)) (c : (Fin D → ι × ℕ) → ℂ)
    (h : ∀ k : Fin D → ℕ, (∀ s, n < k s) → Function.Injective k →
      ∑ w ∈ T, c w * slotTerm q w k = 0) :
    ∀ w ∈ T, c w = 0 := by
  classical
  set S : Finset (Fin D → ι) := T.image slotNode with hS
  set Z : (Fin D → ι) → Fin D → ℂ := fun v s => q (v s) with hZ
  set P : (Fin D → ι) → MvPolynomial (Fin D) ℂ := fun v =>
    ∑ w ∈ T.filter (fun w => slotNode w = v),
      c w • ((descProdSymbol (slotOrder w)).map (Int.castRingHom ℂ)) with hP
  have hZ0 : ∀ v s, Z v s ≠ 0 := fun v s => hq0 (v s)
  have hZinj : Set.InjOn Z ↑S := by
    intro v _ v' _ hvv
    funext s
    exact hqinj (congrFun hvv s)
  have hevalP : ∀ (v : Fin D → ι) (k : Fin D → ℕ),
      MvPolynomial.eval (fun s => ((k s : ℕ) : ℂ)) (P v)
        = ∑ w ∈ T.filter (fun w => slotNode w = v),
            c w * ∏ s, (((k s).descFactorial ((w s).2) : ℕ) : ℂ) := by
    intro v k
    rw [hP, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [MvPolynomial.smul_eval, eval_descProdSymbol_map]
    rfl
  have hmaps : ∀ w ∈ T, slotNode w ∈ S := fun w hw => Finset.mem_image_of_mem _ hw
  have hsum : ∀ k : Fin D → ℕ,
      (∑ v ∈ S, (MvPolynomial.eval (fun s => ((k s : ℕ) : ℂ)) (P v)) * ∏ s, (Z v s) ^ (k s))
        = ∑ w ∈ T, c w * slotTerm q w k := by
    intro k
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun w => c w * slotTerm q w k)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hevalP v k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hnd : slotNode w = v := (Finset.mem_filter.mp hw).2
    rw [slotTerm, hZ]
    have hz : (∏ s, (q (v s)) ^ (k s)) = ∏ s, (q (w s).1) ^ (k s) := by
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [← hnd]
      rfl
    rw [hz]
    ring
  have hPzero : ∀ v ∈ S, P v = 0 := by
    refine mvPolynomial_nodeSeparation_injective S Z hZ0 hZinj P n ?_
    intro k hk hkinj
    rw [hsum k]
    exact h k hk hkinj
  intro w hw
  have hvS : slotNode w ∈ S := hmaps w hw
  have h0 := hPzero (slotNode w) hvS
  set F : Finset (Fin D → ι × ℕ) := T.filter (fun u => slotNode u = slotNode w) with hF
  have hwF : w ∈ F := Finset.mem_filter.mpr ⟨hw, rfl⟩
  have hinjF : ∀ u ∈ F, ∀ u' ∈ F, slotOrder u = slotOrder u' → u = u' := by
    intro u hu u' hu' hord
    have h1 : slotNode u = slotNode w := (Finset.mem_filter.mp hu).2
    have h2 : slotNode u' = slotNode w := (Finset.mem_filter.mp hu').2
    exact slotSeq_ext (h1.trans h2.symm) hord
  set d : (Fin D → ℕ) → ℂ := fun μ =>
    ∑ u ∈ F.filter (fun u => slotOrder u = μ), c u with hd
  have hPv : P (slotNode w)
      = ∑ u ∈ F, c u • ((descProdSymbol (slotOrder u)).map (Int.castRingHom ℂ)) := by
    simp only [hP, hF]
  have hreindex : (∑ u ∈ F, c u • ((descProdSymbol (slotOrder u)).map (Int.castRingHom ℂ)))
      = ∑ μ ∈ F.image slotOrder, d μ • ((descProdSymbol μ).map (Int.castRingHom ℂ)) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun u hu => Finset.mem_image_of_mem slotOrder hu)
      (fun u => c u • ((descProdSymbol (slotOrder u)).map (Int.castRingHom ℂ)))]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [hd]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [(Finset.mem_filter.mp hu).2]
  rw [hPv, hreindex] at h0
  have hzero := descProdSymbol_combination_eq_zero (F.image slotOrder) d h0
    (slotOrder w) (Finset.mem_image_of_mem _ hwF)
  have hsingle : F.filter (fun u => slotOrder u = slotOrder w) = {w} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hwF, rfl⟩, ?_⟩
    intro u hu
    obtain ⟨huF, hord⟩ := Finset.mem_filter.mp hu
    exact hinjF u huF w hwF hord
  simp only [hd] at hzero
  rw [hsingle, Finset.sum_singleton] at hzero
  exact hzero

/-- **Grouped form of the slot-sequence separation.**  When the contributions are indexed by an
arbitrary finite family carrying slot sequences, the total coefficient of each slot sequence
vanishes. -/
theorem slotSequence_grouped_eq_zero {A : Type*} [DecidableEq A] (q : ι → ℂ) (hq0 : ∀ i, q i ≠ 0)
    (hqinj : Function.Injective q) (n : ℕ)
    (T : Finset A) (w : A → (Fin D → ι × ℕ)) (c : A → ℂ)
    (h : ∀ k : Fin D → ℕ, (∀ s, n < k s) → Function.Injective k →
      ∑ a ∈ T, c a * slotTerm q (w a) k = 0)
    (ν : Fin D → ι × ℕ) :
    ∑ a ∈ T.filter (fun a => w a = ν), c a = 0 := by
  classical
  set c' : (Fin D → ι × ℕ) → ℂ := fun u => ∑ a ∈ T.filter (fun a => w a = u), c a with hc'
  have hgroup : ∀ k : Fin D → ℕ,
      (∑ u ∈ T.image w, c' u * slotTerm q u k) = ∑ a ∈ T, c a * slotTerm q (w a) k := by
    intro k
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun a ha => Finset.mem_image_of_mem w ha) (fun a => c a * slotTerm q (w a) k)]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [hc']
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.mp ha).2]
  have hzero := slotSequence_coeff_eq_zero q hq0 hqinj n (T.image w) c' ?_
  · by_cases hν : ν ∈ T.image w
    · have := hzero ν hν
      simpa only [hc'] using this
    · refine Finset.sum_eq_zero fun a ha => ?_
      obtain ⟨haT, haw⟩ := Finset.mem_filter.mp ha
      exact absurd (haw ▸ Finset.mem_image_of_mem w haT) hν
  · intro k hk hkinj
    rw [hgroup k]
    exact h k hk hkinj

end

end GaloisForLFunctions.HTGeometry
