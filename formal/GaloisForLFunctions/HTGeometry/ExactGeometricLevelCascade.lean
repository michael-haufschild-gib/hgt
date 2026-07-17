import GaloisForLFunctions.HTGeometry.GeometricProfileAsymptotics

/-!
# Exact finite geometric level cascade

A finite polynomial-weighted identity graded by distinct geometric exponential scales cannot
cancel between different grades.  The least grade is isolated by exponential separation, its
grouped polynomial vanishes, and strong induction removes it from the exact identity.  This is the
algebraic-analytic engine used by periodic geometric Taylor profiles; no level convergence is
assumed as input.
-/

namespace GaloisForLFunctions

open Filter Finset Polynomial Topology

noncomputable section

def exactGeometricLevelPolynomial
    {α : Type*} [DecidableEq α] (S : Finset α)
    (level : α → ℝ) (weight : α → ℂ[X]) (phase : α → ℂ)
    (v : ℝ) : ℂ[X] :=
  ∑ a ∈ S.filter (fun a => level a = v), C (phase a) * weight a

/-- A remainder which is negligible after rescaling by every represented level does not affect the
level cascade.  This is the form used when a finite pattern window has an exponentially separated
active-atom complement. -/
theorem finite_exactGeometricLevel_cascade_of_remainder
    {α : Type*} [DecidableEq α] (S : Finset α)
    (level : α → ℝ) (weight : α → ℂ[X]) (phase : α → ℂ)
    {A lam : ℝ} (hA : 0 < A) (hlam : 1 < lam)
    (remainder : ℕ → ℂ)
    (hidentity : ∀ q : ℕ,
      ∑ a ∈ S, (weight a).eval (q : ℂ) * phase a *
        ((Real.exp (-A * level a * lam ^ q) : ℝ) : ℂ) + remainder q = 0)
    (hremainder : ∀ v ∈ S.image level,
      Tendsto (fun q : ℕ =>
        ((Real.exp (A * v * lam ^ q) : ℝ) : ℂ) * remainder q)
        atTop (nhds 0)) :
    ∀ v : ℝ, exactGeometricLevelPolynomial S level weight phase v = 0 := by
  classical
  revert hidentity hremainder
  refine Finset.strongInductionOn S ?_
  intro T ih hidentity hremainder v
  by_cases hT : T.Nonempty
  ·
        let values := T.image level
        have hvalues : values.Nonempty := hT.image level
        let m := values.min' hvalues
        let Face := T.filter (fun a => level a = m)
        have hFace : Face.Nonempty := by
          have hm : m ∈ values := Finset.min'_mem values hvalues
          obtain ⟨a, ha, halevel⟩ := Finset.mem_image.mp hm
          refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩⟩
          exact halevel
        have hFaceT : Face ⊆ T := Finset.filter_subset _ _
        have hmle : ∀ a ∈ T, m ≤ level a := by
          intro a ha
          exact Finset.min'_le values (level a)
            (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
        let scaledTerm : ℕ → α → ℂ := fun q a =>
          (weight a).eval (q : ℂ) * phase a *
            ((Real.exp (-A * (level a - m) * lam ^ q) : ℝ) : ℂ)
        have hscaledZero : ∀ q : ℕ,
            (∑ a ∈ T, scaledTerm q a) +
              ((Real.exp (A * m * lam ^ q) : ℝ) : ℂ) * remainder q = 0 := by
          intro q
          calc
            (∑ a ∈ T, scaledTerm q a) +
                ((Real.exp (A * m * lam ^ q) : ℝ) : ℂ) * remainder q =
                ((Real.exp (A * m * lam ^ q) : ℝ) : ℂ) *
                  ((∑ a ∈ T, (weight a).eval (q : ℂ) * phase a *
                    ((Real.exp (-A * level a * lam ^ q) : ℝ) : ℂ)) +
                      remainder q) := by
              rw [mul_add, Finset.mul_sum]
              congr 1
              apply Finset.sum_congr rfl
              intro a ha
              dsimp [scaledTerm]
              push_cast
              have hexp :
                  Complex.exp ((-(A : ℂ)) * ((level a : ℂ) - (m : ℂ)) * (lam : ℂ) ^ q) =
                    Complex.exp ((A : ℂ) * (m : ℂ) * (lam : ℂ) ^ q) *
                      Complex.exp (-((A : ℂ) * (level a : ℂ) * (lam : ℂ) ^ q)) := by
                rw [← Complex.exp_add]
                congr 1
                ring
              rw [hexp]
              ring
            _ = 0 := by rw [hidentity q, mul_zero]
        have hterm : ∀ a ∈ T \ Face,
            Tendsto (fun q : ℕ => scaledTerm q a) atTop (nhds 0) := by
          intro a ha
          have haT : a ∈ T := (Finset.mem_sdiff.mp ha).1
          have haNot : a ∉ Face := (Finset.mem_sdiff.mp ha).2
          have hlevelne : level a ≠ m := by
            intro heq
            exact haNot (Finset.mem_filter.mpr ⟨haT, heq⟩)
          have hlevel : m < level a := lt_of_le_of_ne (hmle a haT) hlevelne.symm
          let gamma := A * (level a - m)
          have hgamma : 0 < gamma := mul_pos hA (sub_pos.mpr hlevel)
          let d := (weight a).natDegree
          have hpoly := tendsto_complexPolynomial_eval_nat_div_pow (weight a)
            (show (weight a).natDegree ≤ d by rfl)
          have hdecayR : Tendsto (fun q : ℕ =>
              ((q : ℝ) ^ d) * Real.exp (-gamma * lam ^ q))
              atTop (nhds 0) := by
            simpa only [Nat.add_zero] using
              tendsto_natAdd_pow_mul_exp_neg_geometric hlam hgamma 0 d
          have hdecayC : Tendsto (fun q : ℕ =>
              ((((q : ℝ) ^ d) * Real.exp (-gamma * lam ^ q) : ℝ) : ℂ))
              atTop (nhds 0) := by
            change Tendsto (Complex.ofReal ∘ fun q : ℕ =>
              ((q : ℝ) ^ d) * Real.exp (-gamma * lam ^ q)) atTop (nhds 0)
            simpa only [map_zero] using
              Complex.continuous_ofReal.continuousAt.tendsto.comp hdecayR
          have hmul := (hpoly.mul hdecayC).mul
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => phase a) atTop (nhds (phase a)))
          have hmul0 : Tendsto (fun q : ℕ =>
              ((weight a).eval (q : ℂ) / (q : ℂ) ^ d) *
                ((((q : ℝ) ^ d) * Real.exp (-gamma * lam ^ q) : ℝ) : ℂ) *
                  phase a) atTop (nhds 0) := by
            simpa using hmul
          apply hmul0.congr'
          filter_upwards [eventually_ge_atTop 1] with q hq
          have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
          dsimp [scaledTerm, gamma]
          push_cast
          field_simp
        have hremTendsto : Tendsto (fun q : ℕ =>
            ∑ a ∈ T \ Face, scaledTerm q a) atTop (nhds 0) := by
          simpa using tendsto_finsetSum (T \ Face) hterm
        let Pface := exactGeometricLevelPolynomial T level weight phase m
        have hPfaceEval : ∀ q : ℕ,
            Pface.eval (q : ℂ) = ∑ a ∈ Face, scaledTerm q a := by
          intro q
          simp only [Pface, exactGeometricLevelPolynomial, Polynomial.eval_finsetSum]
          apply Finset.sum_congr
          · ext a
            simp [Face]
          · intro a ha
            rw [Polynomial.eval_mul, Polynomial.eval_C]
            have halevel : level a = m := (Finset.mem_filter.mp ha).2
            dsimp [scaledTerm]
            rw [halevel]
            simp
            ring
        have hPfaceTendsto : Tendsto (fun q : ℕ => Pface.eval (q : ℂ))
            atTop (nhds 0) := by
          have hmMem : m ∈ T.image level := Finset.min'_mem values hvalues
          have hscaledRemainder := hremainder m hmMem
          have hbalance : ∀ q : ℕ,
              ∑ a ∈ Face, scaledTerm q a =
                -((∑ a ∈ T \ Face, scaledTerm q a) +
                  ((Real.exp (A * m * lam ^ q) : ℝ) : ℂ) * remainder q) := by
            intro q
            have hsplit := Finset.sum_sdiff hFaceT (f := scaledTerm q)
            have hz := hscaledZero q
            calc
              ∑ a ∈ Face, scaledTerm q a =
                  ((∑ a ∈ T \ Face, scaledTerm q a) +
                    ∑ a ∈ Face, scaledTerm q a +
                      ((Real.exp (A * m * lam ^ q) : ℝ) : ℂ) * remainder q) -
                    ((∑ a ∈ T \ Face, scaledTerm q a) +
                      ((Real.exp (A * m * lam ^ q) : ℝ) : ℂ) * remainder q) := by ring
              _ = -((∑ a ∈ T \ Face, scaledTerm q a) +
                    ((Real.exp (A * m * lam ^ q) : ℝ) : ℂ) * remainder q) := by
                rw [hsplit, hz]
                ring
          have hneg := (hremTendsto.add hscaledRemainder).neg
          have hneg0 : Tendsto (fun q : ℕ =>
              -((∑ a ∈ T \ Face, scaledTerm q a) +
                ((Real.exp (A * m * lam ^ q) : ℝ) : ℂ) * remainder q))
              atTop (nhds 0) := by
            simpa using hneg
          apply hneg0.congr'
          filter_upwards with q
          rw [hPfaceEval q, hbalance q]
        have hPfaceZero : Pface = 0 := by
          exact polynomial_eq_zero_of_tendsto_zero Pface (fun q => q)
            strictMono_id hPfaceTendsto
        let R := T \ Face
        have hRssub : R ⊂ T := Finset.sdiff_ssubset hFaceT hFace
        have hfaceOriginal : ∀ q : ℕ,
            ∑ a ∈ Face, (weight a).eval (q : ℂ) * phase a *
              ((Real.exp (-A * level a * lam ^ q) : ℝ) : ℂ) = 0 := by
          intro q
          have heval : Pface.eval (q : ℂ) = 0 := by rw [hPfaceZero, Polynomial.eval_zero]
          calc
            ∑ a ∈ Face, (weight a).eval (q : ℂ) * phase a *
                ((Real.exp (-A * level a * lam ^ q) : ℝ) : ℂ) =
                ((Real.exp (-A * m * lam ^ q) : ℝ) : ℂ) * Pface.eval (q : ℂ) := by
              rw [hPfaceEval q]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a ha
              have halevel : level a = m := (Finset.mem_filter.mp ha).2
              dsimp [scaledTerm]
              rw [halevel]
              simp
              ring
            _ = 0 := by rw [heval, mul_zero]
        have hidentityR : ∀ q : ℕ,
            ∑ a ∈ R, (weight a).eval (q : ℂ) * phase a *
              ((Real.exp (-A * level a * lam ^ q) : ℝ) : ℂ) + remainder q = 0 := by
          intro q
          have hsplit := Finset.sum_sdiff hFaceT
            (f := fun a => (weight a).eval (q : ℂ) * phase a *
              ((Real.exp (-A * level a * lam ^ q) : ℝ) : ℂ))
          dsimp [R]
          rw [hfaceOriginal q, add_zero] at hsplit
          rw [hsplit]
          exact hidentity q
        have hremainderR : ∀ w ∈ R.image level,
            Tendsto (fun q : ℕ =>
              ((Real.exp (A * w * lam ^ q) : ℝ) : ℂ) * remainder q)
              atTop (nhds 0) := by
          intro w hw
          apply hremainder w
          obtain ⟨a, haR, haw⟩ := Finset.mem_image.mp hw
          exact Finset.mem_image.mpr ⟨a, (Finset.mem_sdiff.mp haR).1, haw⟩
        by_cases hvm : v = m
        · subst v
          simpa [Pface] using hPfaceZero
        · have hR := ih R hRssub hidentityR hremainderR v
          have hfilter : T.filter (fun a => level a = v) =
              R.filter (fun a => level a = v) := by
            ext a
            constructor
            · intro ha
              have haT := (Finset.mem_filter.mp ha).1
              have hav := (Finset.mem_filter.mp ha).2
              apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_sdiff.mpr ⟨haT, ?_⟩, hav⟩
              intro haFace
              have ham := (Finset.mem_filter.mp haFace).2
              exact hvm (hav.symm.trans ham)
            · intro ha
              have haR := (Finset.mem_filter.mp ha).1
              have hav := (Finset.mem_filter.mp ha).2
              exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp haR).1, hav⟩
          simpa [exactGeometricLevelPolynomial, hfilter] using hR
  ·
        have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
        subst T
        simp [exactGeometricLevelPolynomial]

/-- Exact finite geometric identities are levelwise polynomial identities. -/
theorem finite_exactGeometricLevel_cascade
    {α : Type*} [DecidableEq α] (S : Finset α)
    (level : α → ℝ) (weight : α → ℂ[X]) (phase : α → ℂ)
    {A lam : ℝ} (hA : 0 < A) (hlam : 1 < lam)
    (hidentity : ∀ q : ℕ,
      ∑ a ∈ S, (weight a).eval (q : ℂ) * phase a *
        ((Real.exp (-A * level a * lam ^ q) : ℝ) : ℂ) = 0) :
    ∀ v : ℝ, exactGeometricLevelPolynomial S level weight phase v = 0 := by
  apply finite_exactGeometricLevel_cascade_of_remainder S level weight phase hA hlam
    (fun _ => 0)
  · intro q
    simpa using hidentity q
  · intro v hv
    simp

/-- **Singleton levels kill.** If every represented weight and phase is nonzero, an exact finite
geometric identity has no valuation level containing exactly one atom. -/
theorem finite_exactGeometricLevel_no_singleton
    {α : Type*} [DecidableEq α] (S : Finset α)
    (level : α → ℝ) (weight : α → ℂ[X]) (phase : α → ℂ)
    {A lam : ℝ} (hA : 0 < A) (hlam : 1 < lam)
    (hphase : ∀ a ∈ S, phase a ≠ 0)
    (hweight : ∀ a ∈ S, weight a ≠ 0)
    (hidentity : ∀ q : ℕ,
      ∑ a ∈ S, (weight a).eval (q : ℂ) * phase a *
        ((Real.exp (-A * level a * lam ^ q) : ℝ) : ℂ) = 0) :
    ∀ v : ℝ, (S.filter fun a => level a = v).card ≠ 1 := by
  intro v hcard
  obtain ⟨a, hface⟩ := Finset.card_eq_one.mp hcard
  have haFace : a ∈ S.filter (fun x => level x = v) := by simp [hface]
  have haS : a ∈ S := (Finset.mem_filter.mp haFace).1
  have hlevel := finite_exactGeometricLevel_cascade S level weight phase hA hlam
    hidentity v
  have hmul : Polynomial.C (phase a) * weight a = 0 := by
    simpa [exactGeometricLevelPolynomial, hface] using hlevel
  rcases mul_eq_zero.mp hmul with hphaseZero | hweightZero
  · apply hphase a haS
    apply Polynomial.C_injective
    simpa using hphaseZero
  · exact hweight a haS hweightZero

end

end GaloisForLFunctions
