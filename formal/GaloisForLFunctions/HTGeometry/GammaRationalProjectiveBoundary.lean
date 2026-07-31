import GaloisForLFunctions.HTGeometry.GammaVerticalDecay
import GaloisForLFunctions.HTGeometry.VerticalStripBohrHull

/-!
# The one-point projective boundary of a Gamma-rational coefficient tuple

Adjoining `Γ` to the digamma field creates a single exponential valuation direction: on an upper
vertical line `Γ → 0`, so a rational expression `P(Γ)/Q(Γ)` is dominated by its lowest Gamma powers
and carries the integer valuation `k = ord₀ P − ord₀ Q`.  Comparing two such expressions, the whole
ratio is `Γ^{k₁−k₂}` times a convergent unit factor.  Consequently, in a finite family, a component
of minimal valuation dominates projectively and all normalized ratios converge: this is eq. (5) for
the subfield `ℂ(Γ) ⊆ K_Γ`.

Everything here is unconditional; the vertical Gamma decay is `Gamma_vertical_tendsto_zero`.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

/-- A polynomial nonvanishing at the origin is nonvanishing near the origin. -/
private theorem eventually_eval_ne_zero (R : Polynomial ℂ) (h : R.eval 0 ≠ 0) :
    ∀ᶠ g : ℂ in nhdsWithin 0 {(0 : ℂ)}ᶜ, R.eval g ≠ 0 :=
  (((Polynomial.continuous R).tendsto 0).mono_left nhdsWithin_le_nhds).eventually
    (isOpen_ne.mem_nhds h)

private theorem div_div_div_of_ne_zero {a b c d : ℂ} (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    a / b / (c / d) = a * d / (b * c) := by
  field_simp

/-- **Separation of the Gamma valuation.**  With `P_j = X^{u_j} R_j` and `Q_j = X^{v_j} S_j`, the
ratio of the two rational expressions is `g^n` times the unit factor `(R₁S₂)/(S₁R₂)`, where
`u₁ + v₂ = n + (u₂ + v₁)`, i.e. `n` is the valuation excess of the first over the second. -/
theorem gammaRational_ratio_eq {g : ℂ} (hg : g ≠ 0) (R₁ S₁ R₂ S₂ : Polynomial ℂ)
    (u₁ v₁ u₂ v₂ n : ℕ) (hn : u₁ + v₂ = n + (u₂ + v₁))
    (hS₁ : S₁.eval g ≠ 0) (hR₂ : R₂.eval g ≠ 0) (hS₂ : S₂.eval g ≠ 0) :
    ((Polynomial.X ^ u₁ * R₁).eval g / (Polynomial.X ^ v₁ * S₁).eval g) /
        ((Polynomial.X ^ u₂ * R₂).eval g / (Polynomial.X ^ v₂ * S₂).eval g)
      = g ^ n * ((R₁.eval g * S₂.eval g) / (S₁.eval g * R₂.eval g)) := by
  have hpow : g ^ u₁ * g ^ v₂ = g ^ n * (g ^ u₂ * g ^ v₁) := by
    rw [← pow_add, ← pow_add, ← pow_add, hn]
  have hgk : ∀ k : ℕ, g ^ k ≠ 0 := fun k => pow_ne_zero k hg
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [div_div_div_of_ne_zero (mul_ne_zero (hgk v₁) hS₁) (mul_ne_zero (hgk u₂) hR₂)
    (mul_ne_zero (hgk v₂) hS₂)]
  have hnum : g ^ u₁ * R₁.eval g * (g ^ v₂ * S₂.eval g)
      = (g ^ u₂ * g ^ v₁) * (g ^ n * (R₁.eval g * S₂.eval g)) := by
    calc g ^ u₁ * R₁.eval g * (g ^ v₂ * S₂.eval g)
        = (g ^ u₁ * g ^ v₂) * (R₁.eval g * S₂.eval g) := by ring
      _ = (g ^ n * (g ^ u₂ * g ^ v₁)) * (R₁.eval g * S₂.eval g) := by rw [hpow]
      _ = (g ^ u₂ * g ^ v₁) * (g ^ n * (R₁.eval g * S₂.eval g)) := by ring
  have hden : g ^ v₁ * S₁.eval g * (g ^ u₂ * R₂.eval g)
      = (g ^ u₂ * g ^ v₁) * (S₁.eval g * R₂.eval g) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ (mul_ne_zero (hgk u₂) (hgk v₁)), mul_div_assoc]

/-- **Projective limit of a Gamma-rational ratio at the exponential boundary.**  As `g → 0` off the
origin, the ratio of two rational expressions tends to `0ⁿ · (R₁(0)S₂(0))/(S₁(0)R₂(0))`: it vanishes
whenever the first has strictly larger valuation (`n > 0`), and converges to the unit residue
quotient when the valuations agree (`n = 0`). -/
theorem gammaRational_ratio_tendsto (R₁ S₁ R₂ S₂ : Polynomial ℂ) (u₁ v₁ u₂ v₂ n : ℕ)
    (hn : u₁ + v₂ = n + (u₂ + v₁))
    (hS₁0 : S₁.eval 0 ≠ 0) (hR₂0 : R₂.eval 0 ≠ 0) (hS₂0 : S₂.eval 0 ≠ 0) :
    Tendsto (fun g : ℂ =>
        ((Polynomial.X ^ u₁ * R₁).eval g / (Polynomial.X ^ v₁ * S₁).eval g) /
          ((Polynomial.X ^ u₂ * R₂).eval g / (Polynomial.X ^ v₂ * S₂).eval g))
      (nhdsWithin 0 {(0 : ℂ)}ᶜ)
      (nhds ((0 : ℂ) ^ n * ((R₁.eval 0 * S₂.eval 0) / (S₁.eval 0 * R₂.eval 0)))) := by
  have hmodel : Tendsto (fun g : ℂ =>
      g ^ n * ((R₁.eval g * S₂.eval g) / (S₁.eval g * R₂.eval g)))
      (nhdsWithin 0 {(0 : ℂ)}ᶜ)
      (nhds ((0 : ℂ) ^ n * ((R₁.eval 0 * S₂.eval 0) / (S₁.eval 0 * R₂.eval 0)))) := by
    have hbase : Tendsto (fun g : ℂ =>
        g ^ n * ((R₁.eval g * S₂.eval g) / (S₁.eval g * R₂.eval g)))
        (nhds 0)
        (nhds ((0 : ℂ) ^ n * ((R₁.eval 0 * S₂.eval 0) / (S₁.eval 0 * R₂.eval 0)))) := by
      refine (tendsto_id.pow n).mul (Tendsto.div ?_ ?_ (mul_ne_zero hS₁0 hR₂0))
      · exact (((Polynomial.continuous R₁).tendsto 0).mul ((Polynomial.continuous S₂).tendsto 0))
      · exact (((Polynomial.continuous S₁).tendsto 0).mul ((Polynomial.continuous R₂).tendsto 0))
    exact hbase.mono_left nhdsWithin_le_nhds
  refine hmodel.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_eval_ne_zero S₁ hS₁0,
    eventually_eval_ne_zero R₂ hR₂0, eventually_eval_ne_zero S₂ hS₂0] with g hg hS₁ hR₂ hS₂
  have hg0 : g ≠ 0 := by simpa using hg
  exact (gammaRational_ratio_eq hg0 R₁ S₁ R₂ S₂ u₁ v₁ u₂ v₂ n hn hS₁ hR₂ hS₂).symm

/-- The completed Gamma value tends to the punctured origin along any vertical return sequence based
at a point of positive abscissa. -/
theorem tendsto_Gamma_along_returns {z₀ : ℂ} (hz : 0 < z₀.re) {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop) :
    Tendsto (fun l => Complex.Gamma (z₀ + (T l : ℂ) * Complex.I)) atTop
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) := by
  have hshift : Tendsto (fun l : ℕ => z₀.im + T l) atTop atTop :=
    tendsto_atTop_add_const_left _ _ hT
  have hcomp := (Gamma_vertical_tendsto_nhdsWithin_zero hz).comp hshift
  refine hcomp.congr (fun l => ?_)
  simp only [Function.comp_apply]
  rw [add_mul_I_eq_ofReal_re_add z₀ (T l)]

/-- A Gamma-rational coefficient of the field `ℂ(Γ)`, presented with its exponential valuation data:
the numerator and denominator polynomials, their orders of vanishing at the origin, and the unit
factors that remain. -/
structure GammaRationalDatum where
  /-- Order of vanishing of the numerator at `Γ = 0`. -/
  numOrder : ℕ
  /-- Order of vanishing of the denominator at `Γ = 0`. -/
  denOrder : ℕ
  /-- Numerator unit factor. -/
  numUnit : Polynomial ℂ
  /-- Denominator unit factor. -/
  denUnit : Polynomial ℂ
  /-- The numerator unit does not vanish at the origin. -/
  numUnit_ne : numUnit.eval 0 ≠ 0
  /-- The denominator unit does not vanish at the origin. -/
  denUnit_ne : denUnit.eval 0 ≠ 0

namespace GammaRationalDatum

/-- The numerator polynomial of the datum. -/
def num (D : GammaRationalDatum) : Polynomial ℂ := Polynomial.X ^ D.numOrder * D.numUnit

/-- The denominator polynomial of the datum. -/
def den (D : GammaRationalDatum) : Polynomial ℂ := Polynomial.X ^ D.denOrder * D.denUnit

/-- The Gamma-rational function attached to the datum. -/
def fn (D : GammaRationalDatum) (s : ℂ) : ℂ :=
  D.num.eval (Complex.Gamma s) / D.den.eval (Complex.Gamma s)

/-- The residue of the datum at the exponential boundary: the ratio of its unit factors at the
origin. -/
def residue (D : GammaRationalDatum) : ℂ := D.numUnit.eval 0 / D.denUnit.eval 0

theorem residue_ne_zero (D : GammaRationalDatum) : D.residue ≠ 0 :=
  div_ne_zero D.numUnit_ne D.denUnit_ne

end GammaRationalDatum

/-- **Projective boundary of a Gamma-rational pair along a vertical return sequence (§4, eq. 5).**
If the valuation of `D₁` exceeds that of `D₂` by `n`, the normalized ratio tends to
`0ⁿ · (residue D₁ / residue D₂)`: to zero when `n > 0`, and to the residue quotient when the
valuations agree. -/
theorem gammaRationalDatum_ratio_tendsto (D₁ D₂ : GammaRationalDatum) (n : ℕ)
    (hn : D₁.numOrder + D₂.denOrder = n + (D₂.numOrder + D₁.denOrder))
    {z₀ : ℂ} (hz : 0 < z₀.re) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun l => D₁.fn (z₀ + (T l : ℂ) * Complex.I) / D₂.fn (z₀ + (T l : ℂ) * Complex.I))
      atTop (nhds ((0 : ℂ) ^ n * (D₁.residue / D₂.residue))) := by
  have hlimit :=
    (gammaRational_ratio_tendsto D₁.numUnit D₁.denUnit D₂.numUnit D₂.denUnit
      D₁.numOrder D₁.denOrder D₂.numOrder D₂.denOrder n hn
      D₁.denUnit_ne D₂.numUnit_ne D₂.denUnit_ne).comp
      (tendsto_Gamma_along_returns hz hT)
  have hres : (D₁.numUnit.eval 0 * D₂.denUnit.eval 0) /
      (D₁.denUnit.eval 0 * D₂.numUnit.eval 0) = D₁.residue / D₂.residue :=
    (div_div_div_of_ne_zero D₁.denUnit_ne D₂.numUnit_ne D₂.denUnit_ne).symm
  rw [← hres]
  exact hlimit

/-- The dominant Gamma-rational coefficient is eventually nonzero along a vertical return sequence:
its numerator and denominator are nonzero because `Γ` is, and the unit factors are nonzero near the
exponential boundary. -/
theorem gammaRationalDatum_eventually_ne_zero (D : GammaRationalDatum)
    {z₀ : ℂ} (hz : 0 < z₀.re) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    ∀ᶠ l in atTop, D.fn (z₀ + (T l : ℂ) * Complex.I) ≠ 0 := by
  have hg := tendsto_Gamma_along_returns hz hT
  filter_upwards [hg.eventually (self_mem_nhdsWithin),
    hg.eventually (eventually_eval_ne_zero D.numUnit D.numUnit_ne),
    hg.eventually (eventually_eval_ne_zero D.denUnit D.denUnit_ne)] with l hgl hnum hden
  have hg0 : Complex.Gamma (z₀ + (T l : ℂ) * Complex.I) ≠ 0 := by simpa using hgl
  have hnum' : D.num.eval (Complex.Gamma (z₀ + (T l : ℂ) * Complex.I)) ≠ 0 := by
    simp only [GammaRationalDatum.num, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X]
    exact mul_ne_zero (pow_ne_zero _ hg0) hnum
  have hden' : D.den.eval (Complex.Gamma (z₀ + (T l : ℂ) * Complex.I)) ≠ 0 := by
    simp only [GammaRationalDatum.den, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X]
    exact mul_ne_zero (pow_ne_zero _ hg0) hden
  exact div_ne_zero hnum' hden'

/-- **Unconditional finite-phase collapse against `ℂ(Γ)` coefficients (§5, eq. 8).**  Let `f` be
holomorphic on the open vertical strip of half-width `η ≤ σ` about `σ` and Bohr almost periodic
there, and let it satisfy a finite differential relation whose coefficients are Gamma-rational,
`∑_α (P_α/Q_α)(Γ) · M_α(f) = 0`, with `β` of minimal exponential valuation — the excess of `α` over
`β` being `n α`.  Then `f` satisfies the autonomous relation obtained by replacing each coefficient
by its projective limit `0^{n α} · (residue α / residue β)`, whose `β`-entry is `1`.

Both analytic inputs are theorems: the return times come from the Bohr hull of the strip, and the
coefficient projective boundary is the vertical Gamma decay. -/
theorem gammaRational_vertical_recurrence_collapse {ι : Type*} (E : Finset ι)
    {σ η : ℝ} (hη : 0 < η) (hση : η ≤ σ) (f : ℂ → ℂ) (exps : ι → (ℕ →₀ ℕ))
    (D : ι → GammaRationalDatum) (β : ι) (hβ : β ∈ E) (n : ι → ℕ)
    (hn : ∀ α ∈ E, (D α).numOrder + (D β).denOrder
      = n α + ((D β).numOrder + (D α).denOrder))
    (hf : DifferentiableOn ℂ f (openVerticalStrip σ η))
    (hap : ∀ η' : ℝ, 0 < η' → η' < η → HasVerticalUniformReturn (closedVerticalStrip σ η') f)
    (hrel : ∀ s : ℂ, ∑ α ∈ E, (D α).fn s * diffMonomial f (exps α) s = 0) :
    ∀ z₀ ∈ openVerticalStrip σ η,
      (∑ α ∈ E, ((0 : ℂ) ^ n α * ((D α).residue / (D β).residue))
          * diffMonomial f (exps α) z₀ = 0) ∧
        (0 : ℂ) ^ n β * ((D β).residue / (D β).residue) = 1 := by
  obtain ⟨T, hT, hmain⟩ :=
    verticalStrip_recurrence_collapse E hη f exps (fun α => (D α).fn) β hβ hf hap hrel
  intro z₀ hz₀
  have hzre : 0 < z₀.re := by
    have habs : |z₀.re - σ| < η := hz₀
    have hlt := (abs_lt.mp habs).1
    linarith
  exact hmain z₀ hz₀ (fun α => (0 : ℂ) ^ n α * ((D α).residue / (D β).residue))
    (gammaRationalDatum_eventually_ne_zero (D β) hzre hT)
    (fun α hα => gammaRationalDatum_ratio_tendsto (D α) (D β) (n α) (hn α hα) hzre hT)

end

end GaloisForLFunctions
