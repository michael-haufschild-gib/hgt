/-
The registration criterion (doc 82 §5, doc 83 — the design gate minted by
the Route C-direct refutation, as a formal object).

A carrier can be part of a creation-counting spine only if its own shallow
pair-zeros force detectable line values — if it REGISTERS its creation. The
universal law behind both directions is the pair-dip law: for the FE∧real
pair factorization Φ = (z − ρ)(z − ρ')·H, ρ = ½ + η + iγ, ρ' = ½ − η + iγ,
the line values obey

  ‖Φ(½+it)‖ = ‖½+it−ρ‖·‖½+it−ρ'‖·‖H(½+it)‖ ≥ η²·‖H(½+it)‖,

with EQUALITY η²·‖H‖ at the foot t = γ. So registration is exactly an
envelope question:

* `pair_dip_foot` — the foot identity (the registration mechanism);
* `pair_dip_lower` — the everywhere lower bound (the obstruction mechanism);
* `RegistersAt` / `RegistrationComplete` — the criterion, as predicates;
* `registersAt_of_envelope_le` / `registrationComplete_of_peeled_envelope`
  — carriers with O(1)-normalized envelopes register (the mollified class:
  κ² = O(1), doc 56 §3);
* `not_registersAt_of_envelope_lower` /
  `not_registrationComplete_of_gap_pair` — **the registration gap,
  formal**: one band pair over an envelope bounded below on its window
  refutes registration below η²·M — the theorem form of doc 82 §1's
  located unsound link (the sharp carrier, κ² ~ log N, fails exactly
  here; so does the exponential-AFE family, E|Z|² ~ log T — doc 83).
-/
import GaloisForLFunctions.RHTower.SeamCongruence

namespace RHTower

open Complex

/-- The right member of an FE∧real pair at height `γ`, offset `η`. -/
noncomputable def pairZero (η γ : ℝ) : ℂ := ((1 / 2 + η : ℝ) : ℂ) + (γ : ℂ) * I

/-- The left (reflected) member of the pair. -/
noncomputable def pairZero' (η γ : ℝ) : ℂ := ((1 / 2 - η : ℝ) : ℂ) + (γ : ℂ) * I

theorem linePoint_sub_pairZero (t η γ : ℝ) :
    linePoint t - pairZero η γ = ((-η : ℝ) : ℂ) + ((t - γ : ℝ) : ℂ) * I := by
  unfold linePoint pairZero
  push_cast
  ring

theorem linePoint_sub_pairZero' (t η γ : ℝ) :
    linePoint t - pairZero' η γ = ((η : ℝ) : ℂ) + ((t - γ : ℝ) : ℂ) * I := by
  unfold linePoint pairZero'
  push_cast
  ring

/-- Distance from the line to the right pair member. -/
theorem norm_linePoint_sub_pairZero (t η γ : ℝ) :
    ‖linePoint t - pairZero η γ‖ = Real.sqrt (η ^ 2 + (t - γ) ^ 2) := by
  rw [linePoint_sub_pairZero, Complex.norm_def, Complex.normSq_add_mul_I]
  ring_nf

/-- Distance from the line to the left pair member. -/
theorem norm_linePoint_sub_pairZero' (t η γ : ℝ) :
    ‖linePoint t - pairZero' η γ‖ = Real.sqrt (η ^ 2 + (t - γ) ^ 2) := by
  rw [linePoint_sub_pairZero', Complex.norm_def, Complex.normSq_add_mul_I]

theorem norm_linePoint_sub_pairZero_ge (t η γ : ℝ) :
    |η| ≤ ‖linePoint t - pairZero η γ‖ := by
  rw [norm_linePoint_sub_pairZero]
  rw [show |η| = Real.sqrt (η ^ 2) from (Real.sqrt_sq_eq_abs η).symm]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (t - γ)])

theorem norm_linePoint_sub_pairZero'_ge (t η γ : ℝ) :
    |η| ≤ ‖linePoint t - pairZero' η γ‖ := by
  rw [norm_linePoint_sub_pairZero']
  rw [show |η| = Real.sqrt (η ^ 2) from (Real.sqrt_sq_eq_abs η).symm]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (t - γ)])

theorem norm_foot_sub_pairZero (η γ : ℝ) :
    ‖linePoint γ - pairZero η γ‖ = |η| := by
  rw [norm_linePoint_sub_pairZero]
  simp [Real.sqrt_sq_eq_abs]

theorem norm_foot_sub_pairZero' (η γ : ℝ) :
    ‖linePoint γ - pairZero' η γ‖ = |η| := by
  rw [norm_linePoint_sub_pairZero']
  simp [Real.sqrt_sq_eq_abs]

/-! ### The pair-dip law -/

/-- **The pair-dip law, lower side (the obstruction mechanism).** Wherever
the pair factorization holds, the line value is at least `η²` times the
envelope. -/
theorem pair_dip_lower {Φ H : ℂ → ℂ} {U : Set ℂ} {η γ : ℝ}
    (hfact : ∀ z ∈ U, Φ z = (z - pairZero η γ) * (z - pairZero' η γ) * H z)
    {t : ℝ} (ht : linePoint t ∈ U) :
    η ^ 2 * ‖H (linePoint t)‖ ≤ ‖Φ (linePoint t)‖ := by
  rw [hfact _ ht, norm_mul, norm_mul]
  have h1 := norm_linePoint_sub_pairZero_ge t η γ
  have h2 := norm_linePoint_sub_pairZero'_ge t η γ
  have hη2 : η ^ 2 = |η| * |η| := by
    rw [← abs_mul, abs_mul_self]
    ring
  rw [hη2]
  have hH : (0 : ℝ) ≤ ‖H (linePoint t)‖ := norm_nonneg _
  have habs : (0 : ℝ) ≤ |η| := abs_nonneg η
  have hab : |η| * |η|
      ≤ ‖linePoint t - pairZero η γ‖ * ‖linePoint t - pairZero' η γ‖ :=
    mul_le_mul h1 h2 habs (le_trans habs h1)
  exact mul_le_mul_of_nonneg_right hab hH

/-- **The pair-dip law, foot identity (the registration mechanism).** At the
pair's own height the line value is EXACTLY `η²` times the envelope. -/
theorem pair_dip_foot {Φ H : ℂ → ℂ} {U : Set ℂ} {η γ : ℝ}
    (hfact : ∀ z ∈ U, Φ z = (z - pairZero η γ) * (z - pairZero' η γ) * H z)
    (hγ : linePoint γ ∈ U) :
    ‖Φ (linePoint γ)‖ = η ^ 2 * ‖H (linePoint γ)‖ := by
  rw [hfact _ hγ, norm_mul, norm_mul, norm_foot_sub_pairZero,
    norm_foot_sub_pairZero']
  rw [show |η| * |η| = η ^ 2 from by rw [← abs_mul, abs_mul_self]; ring]

/-! ### The criterion -/

/-- The carrier registers at height `γ`: some line value within the
`w`-window is at most `lam`. -/
def RegistersAt (Φ : ℂ → ℂ) (γ w lam : ℝ) : Prop :=
  ∃ t : ℝ, |t - γ| ≤ w ∧ ‖Φ (linePoint t)‖ ≤ lam

/-- **The registration criterion.** Over a family `P` of band pairs
(`P η γ` = the carrier has an FE∧real pair at offset `η`, height `γ`), the
carrier registers every pair of the sliver band `0 < η ≤ h` inside its
`w`-window at threshold `lam`. -/
def RegistrationComplete (Φ : ℂ → ℂ) (P : ℝ → ℝ → Prop)
    (h w lam : ℝ) : Prop :=
  ∀ η γ : ℝ, P η γ → 0 < η → η ≤ h → RegistersAt Φ γ w lam

/-- **Registration from an envelope upper bound**: a band pair whose
envelope is at most `M` at the foot registers at `h²·M` (witness: the foot
itself). This is the mollified-class clause — `κ² = O(1)` carriers have
`O(1)`-normalized envelopes. -/
theorem registersAt_of_envelope_le {Φ H : ℂ → ℂ} {U : Set ℂ}
    {η γ h w M : ℝ} (hw : 0 ≤ w) (hη : 0 < η) (hηh : η ≤ h)
    (hfact : ∀ z ∈ U, Φ z = (z - pairZero η γ) * (z - pairZero' η γ) * H z)
    (hγU : linePoint γ ∈ U)
    (hM : ‖H (linePoint γ)‖ ≤ M) :
    RegistersAt Φ γ w (h ^ 2 * M) := by
  refine ⟨γ, by simpa using hw, ?_⟩
  rw [pair_dip_foot hfact hγU]
  have hsq : η ^ 2 ≤ h ^ 2 := by nlinarith
  exact mul_le_mul hsq hM (norm_nonneg _) (by nlinarith)

/-- **The registration gap, formal** (doc 82 §1 as a theorem): a pair whose
envelope is bounded BELOW by `M` throughout its window cannot register below
`η²·M`. -/
theorem not_registersAt_of_envelope_lower {Φ H : ℂ → ℂ} {U : Set ℂ}
    {η γ w M lam : ℝ}
    (hfact : ∀ z ∈ U, Φ z = (z - pairZero η γ) * (z - pairZero' η γ) * H z)
    (hU : ∀ t : ℝ, |t - γ| ≤ w → linePoint t ∈ U)
    (hM : ∀ t : ℝ, |t - γ| ≤ w → M ≤ ‖H (linePoint t)‖)
    (hlam : lam < η ^ 2 * M) :
    ¬ RegistersAt Φ γ w lam := by
  rintro ⟨t, htw, hval⟩
  have hlow := pair_dip_lower hfact (hU t htw)
  have henv := hM t htw
  have : η ^ 2 * M ≤ ‖Φ (linePoint t)‖ := by
    calc η ^ 2 * M ≤ η ^ 2 * ‖H (linePoint t)‖ := by nlinarith [sq_nonneg η]
      _ ≤ ‖Φ (linePoint t)‖ := hlow
  linarith

/-- **Registration completeness from peeled envelopes**: if every band pair
of the family peels with a foot envelope at most `M`, the carrier is
registration-complete at threshold `h²·M`. -/
theorem registrationComplete_of_peeled_envelope {Φ : ℂ → ℂ}
    {P : ℝ → ℝ → Prop} {h w M : ℝ} (hw : 0 ≤ w)
    (hpeel : ∀ η γ, P η γ → 0 < η → η ≤ h →
      ∃ (H : ℂ → ℂ) (U : Set ℂ),
        (∀ z ∈ U, Φ z = (z - pairZero η γ) * (z - pairZero' η γ) * H z) ∧
        linePoint γ ∈ U ∧ ‖H (linePoint γ)‖ ≤ M) :
    RegistrationComplete Φ P h w (h ^ 2 * M) := by
  intro η γ hP hη hηh
  obtain ⟨H, U, hfact, hγU, hM⟩ := hpeel η γ hP hη hηh
  exact registersAt_of_envelope_le hw hη hηh hfact hγU hM

/-- **Registration incompleteness from one gap pair**: a single band pair
over an envelope bounded below on its window refutes registration
completeness below `η²·M` — the theorem form of the Route C-direct
refutation's unsound link. -/
theorem not_registrationComplete_of_gap_pair {Φ H : ℂ → ℂ} {U : Set ℂ}
    {P : ℝ → ℝ → Prop} {h w M lam η γ : ℝ}
    (hP : P η γ) (hη : 0 < η) (hηh : η ≤ h)
    (hfact : ∀ z ∈ U, Φ z = (z - pairZero η γ) * (z - pairZero' η γ) * H z)
    (hU : ∀ t : ℝ, |t - γ| ≤ w → linePoint t ∈ U)
    (hM : ∀ t : ℝ, |t - γ| ≤ w → M ≤ ‖H (linePoint t)‖)
    (hlam : lam < η ^ 2 * M) :
    ¬ RegistrationComplete Φ P h w lam := by
  intro hcomp
  exact not_registersAt_of_envelope_lower hfact hU hM hlam
    (hcomp η γ hP hη hηh)

end RHTower
