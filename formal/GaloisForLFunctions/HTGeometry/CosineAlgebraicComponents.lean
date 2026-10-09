import GaloisForLFunctions.HTGeometry.CosineTwoPoleSequence
import GaloisForLFunctions.HTGeometry.CosineFiniteFibers
import GaloisForLFunctions.HTGeometry.AlgebraicInfinityBranch
import Mathlib.Analysis.Meromorphic.Order

/-!
# Every non-coordinate algebraic curve meets the cosine pair off the integers

Let `T(w) = cos(2π √((w+1/12)/27))` (the entire even series `source`) and `Φ(w) = (T(w), T(-w))`.
For every irreducible plane curve `D = {P = 0}` that is neither vertical nor horizontal and every
finite set `B` of points, the set of non-integral `w` with `Φ(w) ∈ D \ B` is infinite.

Proof: a normalized chart at infinity `(s^{-N}, f(s))` of `D` exists.  If `f` has a pole, the
two-pole conic branch produces points `w_n` with `Φ(w_n)` on the chart, eventually nonreal and
escaping every finite set.  Otherwise `f` extends analytically and is nonconstant; the
finite-coordinate branch (after reflecting `w`) produces chart points which are not eventually
integral and escape every finite set.  In both cases finitely many off-integer points would be
eventually avoided while being hit, a contradiction.
-/

namespace GaloisForLFunctions.HTGeometry.CosineAlgebraicComponents

open Complex Filter LabeledCosineDescent AlgebraicFiniteJetBranch AlgebraicReciprocalParameter
  AlgebraicInfinityBranch
open scoped Topology

noncomputable section

/-- The cosine pair `Φ(w) = (T(w), T(-w))`. -/
def cosinePair (w : ℂ) : ℂ × ℂ := (source w, source (-w))

/-- Non-integral points whose cosine pair lies on `{P = 0}` outside the finite set `B`. -/
def offIntegerFiber (P : BiPoly) (B : Finset (ℂ × ℂ)) : Set ℂ :=
  {w | evalAt P (source w) (source (-w)) = 0 ∧ cosinePair w ∉ B ∧
    w ∉ Set.range (Int.cast : ℤ → ℂ)}

private theorem infinite_of_frequently {S : Set ℂ} {w : ℕ → ℂ} (hfreq : ∃ᶠ n in atTop, w n ∈ S)
    (hesc : ∀ E : Finset ℂ, ∀ᶠ n in atTop, w n ∉ E) : S.Infinite := by
  intro hfin
  obtain ⟨n, h1, h2⟩ := (hfreq.and_eventually (hesc hfin.toFinset)).exists
  exact h2 (hfin.mem_toFinset.mpr h1)

private theorem tendsto_punctured {s : ℕ → ℂ} (hs : Tendsto s atTop (𝓝 0)) (hs0 : ∀ n, s n ≠ 0) :
    Tendsto s atTop (𝓝[≠] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨hs, Eventually.of_forall hs0⟩

private theorem not_int_of_im_ne_zero {w : ℂ} (h : w.im ≠ 0) :
    w ∉ Set.range (Int.cast : ℤ → ℂ) := by
  rintro ⟨k, rfl⟩
  exact h (by simp)

/-- **Theorem A.**  For every irreducible plane curve with positive degree in both coordinates and
every finite set of excluded points, infinitely many non-integral `w` have `Φ(w)` on the curve
outside the excluded points. -/
theorem offIntegerFiber_infinite (P : BiPoly) (hirr : Irreducible P) (hx : 0 < parameterDegree P)
    (hy : 0 < P.natDegree) (B : Finset (ℂ × ℂ)) : (offIntegerFiber P B).Infinite := by
  obtain ⟨N, f, hN, -, hf, hroot, hnc, -⟩ := exists_meromorphic_infinity_chart P hirr hx hy
  set Bx : Finset ℂ := B.image Prod.fst with hBx
  have hpair : ∀ {w : ℂ}, source w ∉ Bx → cosinePair w ∉ B := fun h hm =>
    h (Finset.mem_image.mpr ⟨_, hm, rfl⟩)
  cases hord : meromorphicOrderAt f 0 with
  | top => exact absurd (meromorphicOrderAt_eq_top_iff.mp hord) (hnc 0)
  | coe n =>
    by_cases hn : 0 ≤ n
    · obtain ⟨g, hg, hfg⟩ := hf.meromorphicOrderAt_nonneg_iff.mp (by rw [hord]; exact_mod_cast hn)
      have hgnc : ∀ c : ℂ, ¬ ∀ᶠ s in 𝓝 (0:ℂ), g s = c := by
        intro c hc
        exact hnc c (hfg.trans (hc.filter_mono nhdsWithin_le_nhds))
      obtain ⟨s, w, hs, hs0, hev, hnotZ, hesc, hescx⟩ :=
        CosineFiniteFibers.exists_off_integer_cosine_pair hg hgnc
          (analyticAt_const (v := (1:ℂ))) one_ne_zero N hN
      have hs2 : Tendsto (fun n => s n ^ 2) atTop (𝓝[≠] 0) :=
        tendsto_punctured (by simpa using hs.pow 2) (fun n => pow_ne_zero 2 (hs0 n))
      apply infinite_of_frequently (w := fun n => -w n)
      · have hgood : ∀ᶠ n in atTop, evalAt P (source (-w n)) (source (- -w n)) = 0 ∧
            cosinePair (-w n) ∉ B := by
          filter_upwards [hev, hs2.eventually hroot, hs2.eventually hfg, hescx Bx]
            with k hk hr hfk hx'
          refine ⟨?_, hpair hx'⟩
          rw [neg_neg, hk.1, hk.2, ← hfk, one_div, pow_mul]
          exact hr
        have hfreq : ∃ᶠ n in atTop, w n ∉ Set.range (Int.cast : ℤ → ℂ) :=
          Filter.not_eventually.mp hnotZ
        refine (hfreq.and_eventually hgood).mono fun k hk => ⟨hk.2.1, hk.2.2, ?_⟩
        rintro ⟨j, hj⟩
        exact hk.1 ⟨-j, by simp [hj]⟩
      · intro E
        filter_upwards [hesc (E.image Neg.neg)] with k hk hmem
        exact hk (Finset.mem_image.mpr ⟨_, hmem, neg_neg _⟩)
    · obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hord
      set r := (-n).toNat with hr
      have hr0 : 0 < r := by omega
      have hnr : n = -(r:ℤ) := by omega
      obtain ⟨s, w, hs, hs0, hev, hescw, hescx⟩ :=
        CosineTwoPoleSequence.exists_nonreal_cosine_pair (A := fun _ => (1:ℂ))
          analyticAt_const one_ne_zero hg hg0 N r hN hr0
      have hsp := tendsto_punctured hs hs0
      apply infinite_of_frequently (w := w)
      · refine Eventually.frequently ?_
        filter_upwards [hev, hsp.eventually hroot, hsp.eventually hfg, hescx Bx]
          with k hk hroot' hfk hx'
        refine ⟨?_, hpair hx', not_int_of_im_ne_zero hk.2.2⟩
        rw [hk.1, hk.2.1, one_div]
        rw [hfk, hnr, sub_zero, zpow_neg, zpow_natCast, smul_eq_mul] at hroot'
        rwa [div_eq_inv_mul]
      · exact hescw

end
end GaloisForLFunctions.HTGeometry.CosineAlgebraicComponents
