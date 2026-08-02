import GaloisForLFunctions.HTGeometry.GammaShiftTubeDatumAlgebra
import GaloisForLFunctions.HTGeometry.GammaShiftClassLaw

/-!
# Sums on a tube: equations (15) and (16) uniformly

A coefficient of eq. (15) is a sum of monomials collected by signature.  On the tube the same
argument works: members outside the dominant signature class are negligible against its shape with
one height threshold for every abscissa, so the sum has the dominant class's datum whenever the
residues of that class do not cancel.

Together with the computed tube signature this gives the uniform datum of the coefficients the law
consumes.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {M lam : ℝ}

/-- **The tube datum of a sum, collected by signature class.** -/
theorem hasShiftTubeDatum_sum_class (hM : 0 < M) (hlam : 0 ≤ lam) {N : ℕ}
    (F : Fin N → ℝ → ℝ → ℂ) (d : Fin N → ℤ) (ω : Fin N → ℝ) (b : Fin N → ℤ) (c : Fin N → ℂ)
    (hdat : ∀ α, HasShiftTubeDatum M lam (F α) (d α) (ω α) (b α) (c α)) (β : Fin N)
    (hdom : ∀ α : Fin N, (d α = d β ∧ ω α = ω β ∧ b α = b β)
      ∨ ShiftShapeDominates (d β) (ω β) (b β) (d α) (ω α) (b α))
    (hclass : (∑ α ∈ Finset.univ.filter
      (fun α : Fin N => d α = d β ∧ ω α = ω β ∧ b α = b β), c α) ≠ 0) :
    HasShiftTubeDatum M lam (fun σ t => ∑ α : Fin N, F α σ t) (d β) (ω β) (b β)
      (∑ α ∈ Finset.univ.filter
        (fun α : Fin N => d α = d β ∧ ω α = ω β ∧ b α = b β), c α) := by
  classical
  refine ⟨hclass, ?_⟩
  have hterm : ∀ α : Fin N, TubeLimit M
      (fun σ t => F α σ t / gammaShiftShape lam σ (d β) (ω β) (b β) t)
      (if (d α = d β ∧ ω α = ω β ∧ b α = b β) then c α else 0) := by
    intro α
    by_cases htie : d α = d β ∧ ω α = ω β ∧ b α = b β
    · rw [if_pos htie]
      obtain ⟨h1, h2, h3⟩ := htie
      refine (hdat α).2.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
      rw [h1, h2, h3]
    · rw [if_neg htie]
      have hsub : ShiftShapeDominates (d β) (ω β) (b β) (d α) (ω α) (b α) :=
        (hdom α).resolve_left htie
      have hzero := tubeLimit_gammaShiftShape_ratio_zero hM hlam hsub
      have hmul := (hdat α).2.mul hzero
      rw [mul_zero] at hmul
      refine hmul.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
      have hσlam : 0 < σ + lam := by linarith
      have hSα : gammaShiftShape lam σ (d α) (ω α) (b α) t ≠ 0 :=
        gammaShiftShape_ne_zero hσlam ht _ _ _
      have hSβ : gammaShiftShape lam σ (d β) (ω β) (b β) t ≠ 0 :=
        gammaShiftShape_ne_zero hσlam ht _ _ _
      field_simp
  have hsum := TubeLimit.finsetSum (Finset.univ : Finset (Fin N)) (fun α _ => hterm α)
  have hval : (∑ α : Fin N, (if (d α = d β ∧ ω α = ω β ∧ b α = b β) then c α else 0))
      = ∑ α ∈ Finset.univ.filter
        (fun α : Fin N => d α = d β ∧ ω α = ω β ∧ b α = b β), c α := by
    rw [Finset.sum_filter]
  rw [hval] at hsum
  refine hsum.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  rw [Finset.sum_div]

/-- **A tube sum with a nonvanishing dominant class has a tube datum.** -/
theorem exists_hasShiftTubeDatum_sum_class (hM : 0 < M) (hlam : 0 ≤ lam) {N : ℕ} (hN : 0 < N)
    (F : Fin N → ℝ → ℝ → ℂ) (d : Fin N → ℤ) (ω : Fin N → ℝ) (b : Fin N → ℤ) (c : Fin N → ℂ)
    (hdat : ∀ α, HasShiftTubeDatum M lam (F α) (d α) (ω α) (b α) (c α))
    (hclass : ∀ β : Fin N, (∀ α : Fin N, (d α = d β ∧ ω α = ω β ∧ b α = b β)
        ∨ ShiftShapeDominates (d β) (ω β) (b β) (d α) (ω α) (b α)) →
      (∑ α ∈ Finset.univ.filter
        (fun α : Fin N => d α = d β ∧ ω α = ω β ∧ b α = b β), c α) ≠ 0) :
    ∃ β : Fin N, HasShiftTubeDatum M lam (fun σ t => ∑ α : Fin N, F α σ t) (d β) (ω β) (b β)
      (∑ α ∈ Finset.univ.filter
        (fun α : Fin N => d α = d β ∧ ω α = ω β ∧ b α = b β), c α) := by
  classical
  obtain ⟨β, hβ⟩ := exists_dominant_shiftShape_index hN d ω b
  exact ⟨β, hasShiftTubeDatum_sum_class hM hlam F d ω b c hdat β hβ (hclass β hβ)⟩

/-- **A normal-form sum of multi-translate monomials has a tube datum.**  This is eq. (15) with the
signature `(16)`, uniformly on the tube. -/
theorem exists_hasShiftTubeDatum_multiMonomialSum_class (hM : 0 < M) {r Mm : ℕ} (hMm : 0 < Mm)
    (lamf : Fin r → ℝ) (hlam : ∀ k, 0 ≤ lamf k) (cc : Fin Mm → ℂ) (hcc : ∀ i, cc i ≠ 0)
    (ee : Fin Mm → Fin r → ℕ) (q p : Fin Mm → Polynomial ℂ) (hq : ∀ i, q i ≠ 0)
    (hp : ∀ i, p i ≠ 0) (bb : Fin Mm → ℤ)
    (hclass : ∀ β : Fin Mm, (∀ i : Fin Mm,
        (multiDegree (ee i) = multiDegree (ee β)
          ∧ multiExponent lamf (ee i) (q i) (p i) = multiExponent lamf (ee β) (q β) (p β)
          ∧ bb i = bb β)
        ∨ ShiftShapeDominates (multiDegree (ee β)) (multiExponent lamf (ee β) (q β) (p β)) (bb β)
            (multiDegree (ee i)) (multiExponent lamf (ee i) (q i) (p i)) (bb i)) →
      (∑ i ∈ multiClass lamf ee q p bb β,
        cc i * ((q i).leadingCoeff / (p i).leadingCoeff)) ≠ 0) :
    ∃ β : Fin Mm, HasShiftTubeDatum M 0
      (fun σ t => multiMonomialSum σ lamf cc ee q p bb t)
      (multiDegree (ee β)) (multiExponent lamf (ee β) (q β) (p β)) (bb β)
      (∑ i ∈ multiClass lamf ee q p bb β,
        cc i * ((q i).leadingCoeff / (p i).leadingCoeff)) := by
  classical
  exact exists_hasShiftTubeDatum_sum_class hM le_rfl hMm
    (fun i σ t => cc i * (∏ k : Fin r, gammaLine (σ + lamf k) t ^ ee i k)
      * ((q i).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        / (p i).eval ((σ : ℂ) + (t : ℂ) * Complex.I))
      * vertLog t ^ bb i)
    (fun i => multiDegree (ee i)) (fun i => multiExponent lamf (ee i) (q i) (p i)) bb
    (fun i => cc i * ((q i).leadingCoeff / (p i).leadingCoeff))
    (fun i => hasShiftTubeDatum_multiMonomial hM lamf hlam (ee i) (hcc i) (hq i) (hp i) (bb i))
    hclass

end

end GaloisForLFunctions.HTGeometry
