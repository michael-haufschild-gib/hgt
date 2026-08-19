import GaloisForLFunctions.HTGeometry.QuasiAbelianPoincareSeries

/-!
# Partial Poincaré series over a lattice complement

Abe's subgroup-rank induction does *not* sum over the whole upper lattice: summing a lower
automorphic form over `Γ` would repeat each value infinitely often.  It sums over a complement of
`ΓH` in `Γ`, so that the `ΓH`-automorphy of the seed is used, not summed.

The resulting partial series is still `Γ`-automorphic, and the reason is purely formal: writing an
upper lattice element as `η + comp w`, the `ΓH`-part is absorbed by the seed's own transformation
law (provided the upper factor restricts to the lower one), and the complement part is a
translation of the summation index.  This is the decomposition `F_B = m_B G + R_B` of the card
`torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness`, before any estimate is made.
-/

open Filter Function Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The complement embedding as a map into the upper lattice. -/
def complementEmbedding {d c : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (hcomp : ∀ z, comp z ∈ Γ)
    (z : Fin c → ℤ) : Γ :=
  ⟨comp z, hcomp z⟩

theorem complementEmbedding_add {d c : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (hcomp : ∀ z, comp z ∈ Γ) (z w : Fin c → ℤ) :
    complementEmbedding comp hcomp (z + w)
      = complementEmbedding comp hcomp z + complementEmbedding comp hcomp w := by
  ext i
  simp [complementEmbedding, map_add]

/-- The partial Poincaré sum over a complement of `ΓH` in `Γ`. -/
def cosetPoincareSeries {d c : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (upper : AutomorphicFactor d Γ) (comp : (Fin c → ℤ) →+ (Fin d → ℂ))
    (hcomp : ∀ z, comp z ∈ Γ) (H : MultivariateEntire d) (x : Fin d → ℂ) : ℂ :=
  ∑' z : Fin c → ℤ, poincareTerm upper H (complementEmbedding comp hcomp z) x

/-- **The partial Poincaré series is `Γ`-automorphic.**  Only the seed's `ΓH`-automorphy and the
compatibility of the two factors are used; no convergence hypothesis is needed, because both
`tsum_mul_left` and the index translation are unconditional. -/
theorem cosetPoincareSeries_shift {d c : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    (lower : AutomorphicFactor d ΓH) (upper : AutomorphicFactor d Γ)
    (hle : ΓH ≤ Γ)
    (hcompat : ∀ (η : Fin d → ℂ) (hη : η ∈ ΓH),
      (upper.factor ⟨η, hle hη⟩).1 = (lower.factor ⟨η, hη⟩).1)
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (hcomp : ∀ z, comp z ∈ Γ)
    (H : MultivariateEntire d) (hH : H ∈ lower.forms)
    {δ : Fin d → ℂ} (hδ : δ ∈ Γ) {η : Fin d → ℂ} (hη : η ∈ ΓH) {w : Fin c → ℤ}
    (hdec : δ = η + comp w) (x : Fin d → ℂ) :
    cosetPoincareSeries upper comp hcomp H (x + δ)
      = (upper.factor ⟨δ, hδ⟩).1 x * cosetPoincareSeries upper comp hcomp H x := by
  classical
  set e : (Fin c → ℤ) → Γ := complementEmbedding comp hcomp with hedef
  have hadd : ∀ z w : Fin c → ℤ, e (z + w) = e z + e w := fun z w =>
    complementEmbedding_add comp hcomp z w
  have hterm : ∀ z : Fin c → ℤ,
      poincareTerm upper H (e z) (x + δ)
        = (upper.factor ⟨δ, hδ⟩).1 x * poincareTerm upper H (e (z + w)) x := by
    intro z
    have hδΓ : (⟨δ, hδ⟩ : Γ) = ⟨η, hle hη⟩ + e w := by
      ext i
      simp [hedef, complementEmbedding, hdec]
    have hsum : e z + (⟨δ, hδ⟩ : Γ) = ⟨η, hle hη⟩ + e (z + w) := by
      rw [hδΓ, hadd]
      abel
    have hcoc := upper.cocycle (e z) ⟨δ, hδ⟩ x
    rw [hsum] at hcoc
    have hcoc2 := upper.cocycle ⟨η, hle hη⟩ (e (z + w)) x
    have hkey : (upper.factor (e z)).1 (x + δ) * (upper.factor ⟨δ, hδ⟩).1 x
        = (upper.factor ⟨η, hle hη⟩).1 (x + (e (z + w)).1)
          * (upper.factor (e (z + w))).1 x := by
      rw [← hcoc, hcoc2]
    have hseed : H.1 (x + δ + (e z).1)
        = (lower.factor ⟨η, hη⟩).1 (x + (e (z + w)).1) * H.1 (x + (e (z + w)).1) := by
      have hxy : x + δ + (e z).1 = (x + (e (z + w)).1) + η := by
        funext i
        simp only [hedef, complementEmbedding, hdec, Pi.add_apply, map_add]
        ring
      rw [hxy]
      exact hH ⟨η, hη⟩ (x + (e (z + w)).1)
    have hcompatη := hcompat η hη
    have hneA := upper.nowhereZero (e z) (x + δ)
    have hneF := upper.nowhereZero (e (z + w)) x
    rw [poincareTerm, poincareTerm, hseed, ← hcompatη]
    have hE : (upper.factor ⟨η, hle hη⟩).1 (x + (e (z + w)).1)
        = (upper.factor (e z)).1 (x + δ) * (upper.factor ⟨δ, hδ⟩).1 x
            / (upper.factor (e (z + w))).1 x := by
      rw [eq_div_iff hneF]
      exact hkey.symm
    rw [hE]
    field_simp
  rw [cosetPoincareSeries, cosetPoincareSeries]
  rw [tsum_congr hterm, tsum_mul_left]
  congr 1
  exact (Equiv.addRight w).tsum_eq (fun z => poincareTerm upper H (e z) x)


theorem continuous_cosetPoincareSeries_of_summableLocallyUniformly
    {d c : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (upper : AutomorphicFactor d Γ) (comp : (Fin c → ℤ) →+ (Fin d → ℂ))
    (hcomp : ∀ z, comp z ∈ Γ) (H : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun z : Fin c → ℤ => poincareTerm upper H (complementEmbedding comp hcomp z)) Set.univ) :
    Continuous (cosetPoincareSeries upper comp hcomp H) := by
  rw [← continuousOn_univ]
  apply hnormal.hasSumLocallyUniformlyOn.continuousOn
  exact (Filter.Eventually.of_forall fun S =>
    (continuous_finsetSum S fun z _ =>
      continuous_poincareTerm upper H (complementEmbedding comp hcomp z)).continuousOn).frequently

theorem lineEntire_cosetPoincareSeries_of_summableLocallyUniformly
    {d c : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (upper : AutomorphicFactor d Γ) (comp : (Fin c → ℤ) →+ (Fin d → ℂ))
    (hcomp : ∀ z, comp z ∈ Γ) (H : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun z : Fin c → ℤ => poincareTerm upper H (complementEmbedding comp hcomp z)) Set.univ) :
    LineEntire ⟨cosetPoincareSeries upper comp hcomp H,
      continuous_cosetPoincareSeries_of_summableLocallyUniformly upper comp hcomp H hnormal⟩ := by
  intro x v
  let line := affineComplexLine x v
  have hline : SummableLocallyUniformlyOn
      (fun z : Fin c → ℤ => fun w =>
        poincareTerm upper H (complementEmbedding comp hcomp z) (line w)) Set.univ :=
    hnormal.comp line (mapsTo_univ _ _) line.continuous.continuousOn
  have hd : DifferentiableOn ℂ
      (fun w => ∑' z : Fin c → ℤ,
        poincareTerm upper H (complementEmbedding comp hcomp z) (line w)) Set.univ := by
    apply hline.hasSumLocallyUniformlyOn.differentiableOn
    · exact Filter.Eventually.of_forall fun S =>
        (Differentiable.fun_sum fun z _ =>
          lineEntire_poincareTerm upper H (complementEmbedding comp hcomp z) x v).differentiableOn
    · exact isOpen_univ
  simpa [cosetPoincareSeries, line, affineComplexLine] using (differentiableOn_univ.mp hd)

/-- The partial Poincaré series as a line-entire source. -/
def cosetPoincareSeriesEntire {d c : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (upper : AutomorphicFactor d Γ) (comp : (Fin c → ℤ) →+ (Fin d → ℂ))
    (hcomp : ∀ z, comp z ∈ Γ) (H : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun z : Fin c → ℤ => poincareTerm upper H (complementEmbedding comp hcomp z)) Set.univ) :
    MultivariateEntire d :=
  ⟨⟨cosetPoincareSeries upper comp hcomp H,
      continuous_cosetPoincareSeries_of_summableLocallyUniformly upper comp hcomp H hnormal⟩,
    lineEntire_cosetPoincareSeries_of_summableLocallyUniformly upper comp hcomp H hnormal⟩

/-- **The partial Poincaré series is an upper automorphic form.** -/
theorem cosetPoincareSeriesEntire_mem_forms {d c : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    (lower : AutomorphicFactor d ΓH) (upper : AutomorphicFactor d Γ)
    (hle : ΓH ≤ Γ)
    (hcompat : ∀ (η : Fin d → ℂ) (hη : η ∈ ΓH),
      (upper.factor ⟨η, hle hη⟩).1 = (lower.factor ⟨η, hη⟩).1)
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (hcomp : ∀ z, comp z ∈ Γ)
    (hdecomp : ∀ δ ∈ Γ, ∃ η ∈ ΓH, ∃ w : Fin c → ℤ, δ = η + comp w)
    (H : MultivariateEntire d) (hH : H ∈ lower.forms)
    (hnormal : SummableLocallyUniformlyOn
      (fun z : Fin c → ℤ => poincareTerm upper H (complementEmbedding comp hcomp z)) Set.univ) :
    cosetPoincareSeriesEntire upper comp hcomp H hnormal ∈ upper.forms := by
  intro γ x
  obtain ⟨η, hη, w, hdec⟩ := hdecomp γ.1 γ.2
  have h := cosetPoincareSeries_shift lower upper hle hcompat comp hcomp H hH γ.2 hη hdec x
  simpa [cosetPoincareSeriesEntire, Subtype.coe_eta] using h

/-- **The Abe decomposition `F = H + R`.**  The complement index `0` contributes the seed itself,
and everything else is the complement-lattice remainder. -/
theorem cosetPoincareSeries_eq_seed_add_tail {d c : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (upper : AutomorphicFactor d Γ) (comp : (Fin c → ℤ) →+ (Fin d → ℂ))
    (hcomp : ∀ z, comp z ∈ Γ) (H : MultivariateEntire d) (x : Fin d → ℂ)
    (hsummable : Summable
      (fun z : Fin c → ℤ => poincareTerm upper H (complementEmbedding comp hcomp z) x)) :
    cosetPoincareSeries upper comp hcomp H x
      = H.1 x
        + ∑' z : Fin c → ℤ,
            (if z = 0 then 0
              else poincareTerm upper H (complementEmbedding comp hcomp z) x) := by
  have hzero : poincareTerm upper H (complementEmbedding comp hcomp 0) x = H.1 x := by
    have hc0 : comp (0 : Fin c → ℤ) = 0 := map_zero comp
    have he0 : complementEmbedding comp hcomp (0 : Fin c → ℤ) = 0 := by
      ext i
      simp [complementEmbedding, hc0]
    rw [poincareTerm, he0]
    have hn := upper.normalized x
    rw [hn]
    simp
  rw [cosetPoincareSeries, hsummable.tsum_eq_add_tsum_ite 0, hzero]

end

end GaloisForLFunctions.HTGeometry
