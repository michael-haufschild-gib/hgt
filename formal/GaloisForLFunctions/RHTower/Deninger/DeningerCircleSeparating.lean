import GaloisForLFunctions.RHTower.Deninger.DeningerFrechetInstances

/-!
# The circle seminorms separate points

The order-zero seminorm of `C^∞(ℝ/Pℤ)` dominates every value of the function, so it vanishes only
on the zero function.  A separating family of seminorms induces a `T₁` — hence, on a topological
group, a `T₂` — topology, and the kernel of the periodization is therefore closed in Meyer's
source.

* `DeningerCircle.seminorms_separating` : **the family separates points.**
* `DeningerCircle.instT2Space`
* `deningerPeriodizationLM_isClosed_ker` : **`K_p = ker Per_p` is closed.**
-/

namespace RHTower

open Filter Topology

namespace DeningerCircle

variable {P : {x : ℝ // 0 < x}}

/-- The order-zero seminorm dominates every value. -/
theorem norm_le_seminorms_zero (F : DeningerCircle P) (t : ℝ) :
    ‖((toPeriodic F : ↥(DeningerSmoothPeriodic P.1)) : ℝ → ℂ) t‖ ≤ seminorms P 0 F := by
  have hb := deningerPeriodicSup_le P.2 0 (toPeriodic F) t
  rw [norm_iteratedFDeriv_zero] at hb
  simpa [seminorms_apply, deningerPeriodicSupLe] using hb

/-- **The `C^r` family separates points.** -/
theorem seminorms_separating (F : DeningerCircle P) (hF : F ≠ 0) : ∃ r : ℕ, seminorms P r F ≠ 0 := by
  refine ⟨0, ?_⟩
  have hne : ∃ t : ℝ, ((toPeriodic F : ↥(DeningerSmoothPeriodic P.1)) : ℝ → ℂ) t ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hF (toPeriodic.injective (Subtype.ext (funext hall)))
  obtain ⟨t, ht⟩ := hne
  have hpos : 0 < ‖((toPeriodic F : ↥(DeningerSmoothPeriodic P.1)) : ℝ → ℂ) t‖ := norm_pos_iff.2 ht
  exact ne_of_gt (lt_of_lt_of_le hpos (norm_le_seminorms_zero F t))

instance instT1Space : T1Space (DeningerCircle P) :=
  (withSeminorms P).T1_of_separating seminorms_separating

instance instT2Space : T2Space (DeningerCircle P) := by infer_instance

end DeningerCircle

/-- **The kernel of the periodization is closed.**  It is the preimage of the closed point `0` of
the Hausdorff circle space under a continuous map. -/
theorem deningerPeriodizationLM_isClosed_ker (P : {x : ℝ // 0 < x}) :
    IsClosed ((LinearMap.ker (deningerPeriodizationLM P) : Submodule ℂ DeningerMeyerSource) :
      Set DeningerMeyerSource) := by
  have hpre : ((LinearMap.ker (deningerPeriodizationLM P) :
      Submodule ℂ DeningerMeyerSource) : Set DeningerMeyerSource)
      = deningerPeriodizationLM P ⁻¹' {0} := by
    ext x
    simp [LinearMap.mem_ker]
  rw [hpre]
  exact (isClosed_singleton (X := DeningerCircle P)).preimage (deningerPeriodizationLM_continuous P)

end RHTower
