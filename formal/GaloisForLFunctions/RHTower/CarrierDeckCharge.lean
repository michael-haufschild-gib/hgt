/-
# The deck charge of an arbitrary carrier

The ξ deck charge `xiDeckCharge` is the case `f = ξ` of one object attached to *any*
analytic carrier: the `μ_{2^k}`-valued monodromy of its `2^k`-th-root torsor,

  `carrierCharge f k ρ = exp(2πi · ord_ρ(f) / 2^k) = deckRed (2^k) (ord_ρ(f))`.

Nothing about ξ enters the definition or the structural laws.  What ξ contributes — the
functional equation and Schwarz reflection — is isolated as *hypotheses*: the charge is
`V₄`-invariant exactly for carriers carrying those two symmetries.  This is the deck-torsor
object in the generality the seam operations need: it turns the root-existence problem for
any carrier on a convex domain into the vanishing of a single observable
(`exists_root_iff_carrierCharge_trivial`), and the Goldilocks question — which carriers
force the charge to vanish off the seam — is posed on `carrierCharge` rather than on ξ's
zeros.

The construction reads a *given* carrier's order; it constructs no carrier and integrates
no loop — the charge is a constraint invariant.
-/
import GaloisForLFunctions.RHTower.RootExistence
import GaloisForLFunctions.RHTower.DeckChargeCalculus
import GaloisForLFunctions.RHTower.Reflection

namespace RHTower

open Complex Filter Set Metric

/-- The level-`2^k` deck charge of a carrier `f` at `ρ`: the monodromy `exp(2πi·ord/2^k)`
of its `2^k`-th-root torsor, read from the vanishing order of `f` at `ρ`. -/
noncomputable def carrierCharge (f : ℂ → ℂ) (k : ℕ) (ρ : ℂ) : ℂ :=
  deckRed (2 ^ k) ((analyticOrderAt f ρ).toNat : ℤ)

/-- The charge is a `2^k`-th root of unity — it lands in `μ_{2^k}`. -/
theorem carrierCharge_pow (f : ℂ → ℂ) (k : ℕ) (ρ : ℂ) :
    carrierCharge f k ρ ^ (2 ^ k) = 1 :=
  deckRed_pow_self (pow_pos (by norm_num) k) _

theorem carrierCharge_ne_zero (f : ℂ → ℂ) (k : ℕ) (ρ : ℂ) : carrierCharge f k ρ ≠ 0 :=
  deckRed_ne_zero _ _

/-- **Triviality reads divisibility.**  The charge is `1` iff `2^k` divides the order. -/
theorem carrierCharge_eq_one_iff_dvd (f : ℂ → ℂ) (k : ℕ) (ρ : ℂ) :
    carrierCharge f k ρ = 1 ↔ 2 ^ k ∣ (analyticOrderAt f ρ).toNat := by
  rw [carrierCharge, deckRed_eq_one_iff (pow_pos (by norm_num) k), Int.natCast_dvd_natCast]

/-- The `ℕ∞` form of the vanishing criterion, at a point of finite order. -/
theorem carrierCharge_eq_one_iff_enat_dvd {f : ℂ → ℂ} {k : ℕ} {ρ : ℂ}
    (hfin : analyticOrderAt f ρ ≠ ⊤) :
    carrierCharge f k ρ = 1 ↔ ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt f ρ := by
  rw [carrierCharge_eq_one_iff_dvd]
  have hcoe : analyticOrderAt f ρ = (((analyticOrderAt f ρ).toNat : ℕ) : ℕ∞) :=
    (ENat.coe_toNat hfin).symm
  constructor
  · intro h; rw [hcoe]; exact Nat.cast_dvd_cast h
  · intro h; rw [hcoe] at h
    exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) h

/-- Off the divisor the charge is trivial: a non-zero has order `0`. -/
theorem carrierCharge_eq_one_of_ne_zero (f : ℂ → ℂ) (k : ℕ) {ρ : ℂ}
    (h : f ρ ≠ 0) : carrierCharge f k ρ = 1 := by
  rw [carrierCharge_eq_one_iff_dvd]
  rw [analyticOrderAt_eq_zero.mpr (Or.inr h)]
  simp

/-- Squaring a level-`2n` deck value gives the level-`n` value. -/
private theorem deckRed_sq_two_mul {n : ℕ} (hn : 0 < n) (m : ℤ) :
    deckRed (2 * n) m ^ 2 = deckRed n m := by
  unfold deckRed
  rw [← Complex.exp_nat_mul]
  congr 1
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  push_cast
  field_simp

/-- **Dyadic coherence.**  `w_{k+1}² = w_k`: the charge descends the `2`-power tower. -/
theorem carrierCharge_succ_sq (f : ℂ → ℂ) (k : ℕ) (ρ : ℂ) :
    carrierCharge f (k + 1) ρ ^ 2 = carrierCharge f k ρ := by
  unfold carrierCharge
  rw [show (2 ^ (k + 1) : ℕ) = 2 * 2 ^ k from by ring,
    deckRed_sq_two_mul (pow_pos (by norm_num) k)]

/-- **Rung 0 is invisible.**  The level-`1` charge is always `1`. -/
theorem carrierCharge_zero (f : ℂ → ℂ) (ρ : ℂ) : carrierCharge f 0 ρ = 1 := by
  have h := carrierCharge_pow f 0 ρ
  simpa using h

/-- **The base level is the parity sign.**  `carrierCharge f 1 ρ = (−1)^{ord}` — the μ₂ face. -/
theorem carrierCharge_one_eq_neg_one_pow (f : ℂ → ℂ) (ρ : ℂ) :
    carrierCharge f 1 ρ = (-1) ^ (analyticOrderAt f ρ).toNat := by
  unfold carrierCharge deckRed
  have harg : 2 * (Real.pi : ℂ) * I * (((analyticOrderAt f ρ).toNat : ℤ) : ℂ) / ((2 ^ 1 : ℕ) : ℂ)
      = (((analyticOrderAt f ρ).toNat : ℕ) : ℂ) * ((Real.pi : ℂ) * I) := by
    push_cast
    ring
  rw [harg, exp_nat_mul, exp_pi_mul_I]

/-! ## The root–charge equivalence, for any carrier -/

/-- **Root existence ⟺ charge triviality.**  On a convex open `Ω` with a marked nonvanishing
point and a locally finite zero set, `f` has an analytic `2^k`-th root on `Ω` iff its deck
charge is trivial at every zero.  This is the deck-torsor form of the Kummer obstruction,
for an arbitrary carrier — no functional equation, no ξ. -/
theorem exists_root_iff_carrierCharge_trivial {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ} {k : ℕ}
    (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hz₀ : z₀ ∈ Ω) (hf : AnalyticOnNhd ℂ f Ω)
    (hf0 : f z₀ ≠ 0)
    (hZloc : ∀ R : ℕ, {s ∈ Ω ∩ ball z₀ ((R : ℝ) + 1) | f s = 0}.Finite) :
    (∃ g, AnalyticOnNhd ℂ g Ω ∧ ∀ s ∈ Ω, g s ^ (2 ^ k) = f s) ↔
      ∀ ρ ∈ Ω, f ρ = 0 → carrierCharge f k ρ = 1 := by
  rw [exists_root_iff_orders_dvd (pow_pos (by norm_num) k) hΩo hΩc hz₀ hf hf0 hZloc]
  have hord : ∀ ρ ∈ Ω, analyticOrderAt f ρ ≠ ⊤ := by
    intro ρ hρ htop
    have hev0 : f =ᶠ[nhds ρ] (0 : ℂ → ℂ) := by
      filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
      simpa using hz
    exact hf0 (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩc.isPreconnected hρ hev0 hz₀)
  refine forall₃_congr fun ρ hρ _ => ?_
  exact (carrierCharge_eq_one_iff_enat_dvd (hord ρ hρ)).symm

/-! ## Symmetry — the `V₄` structure is exactly the two carrier symmetries -/

/-- **Schwarz invariance.**  For a conjugation-equivariant carrier (`f(s̄) = \overline{f(s)}`),
the charge is invariant under `ρ ↦ ρ̄`. -/
theorem carrierCharge_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconj : ∀ s, f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (f s)) (k : ℕ) (ρ : ℂ) :
    carrierCharge f k ((starRingEnd ℂ) ρ) = carrierCharge f k ρ := by
  unfold carrierCharge
  have hfun : (fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) = f := by
    funext w; rw [hconj, Complex.conj_conj]
  have h := analyticOrderAt_conj_conj hf ρ
  rw [hfun] at h
  rw [h]

/-- **FE invariance.**  For a carrier with the functional equation `f(1−s) = f(s)`, the charge
is invariant under `ρ ↦ 1 − ρ`. -/
theorem carrierCharge_one_sub {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfe : ∀ s, f (1 - s) = f s) (k : ℕ) (ρ : ℂ) :
    carrierCharge f k (1 - ρ) = carrierCharge f k ρ := by
  unfold carrierCharge
  have hfun : (fun w => f (1 - w)) = f := by funext w; exact hfe w
  have h := analyticOrderAt_comp_one_sub hf ρ
  rw [hfun] at h
  rw [h]

/-- **`V₄`-invariance.**  A carrier with both the functional equation and Schwarz reflection
has a charge constant on the quadruple `{ρ, 1−ρ, ρ̄, 1−ρ̄}`: the deck charge is a `V₄`-invariant
of the FE-symmetric carrier, whatever the carrier is. -/
theorem carrierCharge_quadruple {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconj : ∀ s, f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (f s))
    (hfe : ∀ s, f (1 - s) = f s) (k : ℕ) (ρ : ℂ) :
    carrierCharge f k (1 - ρ) = carrierCharge f k ρ ∧
      carrierCharge f k ((starRingEnd ℂ) ρ) = carrierCharge f k ρ ∧
      carrierCharge f k (1 - (starRingEnd ℂ) ρ) = carrierCharge f k ρ := by
  refine ⟨carrierCharge_one_sub hf hfe k ρ, carrierCharge_conj hf hconj k ρ, ?_⟩
  rw [carrierCharge_one_sub hf hfe, carrierCharge_conj hf hconj]

end RHTower
