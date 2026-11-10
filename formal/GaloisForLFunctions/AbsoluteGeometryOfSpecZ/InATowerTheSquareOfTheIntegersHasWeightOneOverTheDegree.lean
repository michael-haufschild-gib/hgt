import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheCountertermOfANumberRingObeysRiemannHurwitz

/-!
# In a tower the square of the integers has weight one over the degree

Over a finite field the Riemann hypothesis of a curve follows from an inequality on the
extensions of the constant field, because the zeta function of the extension is made of the
zeta function of the base. Over `ℤ` an extension of the base is a cover with ramification: the
zeta function of a ring of degree `d` is `ζ(s)` times `d − 1` twisted factors, and `ζ` is the
fixed part. This file states what that does to the pairing of the squares along a tower.

* **The weight of the base** (`CharacterRing`, `tendsto_ringZeroSum_div_degree_sub`). For rings
  `K_k` given by their primitive characters, of degrees `d_k → ∞`, the defect of the pairing per
  degree, `Z_{K_k}(f)/d_k`, differs from the mean of the twisted parts by `Z_ζ(f)/d_k → 0`, on
  every packet.
* **The limit inequality does not see `ζ`** (`eventually_neg_le_ringZeroSum_div_degree`,
  `eventually_ringPairing_div_degree_le`). If the twisted parts of the rings are nonnegative on
  a packet, the defect per degree is eventually above `−ε`, and the limit of the pairing per
  degree is at most the pole term per degree plus `ε`, whatever the zeros of `ζ` are. At each
  finite stage the inequality on the square of the ring implies the Riemann hypothesis
  (`riemannHypothesis_of_ringDefect`); per degree, in the limit, that is lost.
* **The cyclotomic tower** (`weightedContact_cyclotomicWeight_eq_zero`,
  `exists_cyclotomicZeroSum_eq`, `exists_forall_cyclotomicZeroSum_ge`). For a prime `p` beyond
  the window no contact of the cyclotomic ring of conductor `p` enters: its ideals have norms
  `≡ 0, 1 (mod p)`. The defect on a packet is then
  `2 d₁ d₂ − (p − 1)A(f) + Σ_χ E_χ(f) + (p − 2) log p ∫f²`, `A(f)` the finite part of the jets
  of the integers and `E_χ` the energies of the complex places: archimedean terms and the
  discriminant. It is at least `(p − 1)(½ log p ∫f² − C_f)`: the inequality holds on every fixed
  packet for all large `p`, and the defect per degree tends to infinity with the root
  discriminant.

So the squares of a tower do not replace the extension of constants: the form of `ζ` enters
the form of the ring with the weight `1/[K:ℚ]`.
-/

open Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt Real
open Zeta23

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Rings given by their characters -/

/-- A number ring given by the nontrivial primitive characters of its zeta function
`ζ(s) Π_i L(s, χ_i)`. -/
structure CharacterRing where
  /-- The index set of the nontrivial characters. -/
  κ : Type
  [fintypeκ : Fintype κ]
  /-- The conductors. -/
  q : κ → ℕ
  [neZeroq : ∀ i, NeZero (q i)]
  one_lt : ∀ i, 1 < q i
  /-- The characters. -/
  χ : ∀ i, DirichletCharacter ℂ (q i)
  primitive : ∀ i, (χ i).IsPrimitive

attribute [instance] CharacterRing.fintypeκ CharacterRing.neZeroq

namespace CharacterRing

/-- The degree of the ring: the number of its characters, the trivial one included. -/
def degree (K : CharacterRing) : ℕ := Fintype.card K.κ + 1

/-- The sum over the zeros of the twisted factors of the zeta function of the ring. -/
def twistedSum (K : CharacterRing) (f : ℝ → ℝ) : ℝ :=
  ∑ i, twistedZeroSum (K.one_lt i) (K.primitive i) f

theorem ringZeroSum_eq (K : CharacterRing) (f : ℝ → ℝ) :
    ringZeroSum K.one_lt K.primitive f = zeroSum f + K.twistedSum f := rfl

theorem degree_pos (K : CharacterRing) : (0 : ℝ) < K.degree := by
  unfold degree
  positivity

end CharacterRing

variable {f : ℝ → ℝ}

/-! ### The weight of the base in a tower -/

/-- The form of `ζ` per degree tends to zero along rings of growing degree. -/
theorem tendsto_zeroSum_div_degree (K : ℕ → CharacterRing)
    (hdeg : Tendsto (fun k => ((K k).degree : ℝ)) atTop atTop) (f : ℝ → ℝ) :
    Tendsto (fun k => zeroSum f / ((K k).degree : ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop hdeg

/-- **The form of `ζ` has weight one over the degree.** Along rings of degrees tending to
infinity the defect of the pairing per degree and the mean of the twisted parts have the same
limit behaviour on every packet: their difference is `Z_ζ(f)/d` and tends to zero. -/
theorem tendsto_ringZeroSum_div_degree_sub (K : ℕ → CharacterRing)
    (hdeg : Tendsto (fun k => ((K k).degree : ℝ)) atTop atTop) (f : ℝ → ℝ) :
    Tendsto (fun k => ringZeroSum (K k).one_lt (K k).primitive f / (K k).degree -
      (K k).twistedSum f / (K k).degree) atTop (𝓝 0) := by
  refine (tendsto_zeroSum_div_degree K hdeg f).congr fun k => ?_
  rw [CharacterRing.ringZeroSum_eq, add_div, add_sub_cancel_right]

/-- **The limit inequality does not see `ζ`.** If the twisted parts of the rings of a tower are
nonnegative on a packet, the defect per degree is eventually above `−ε`. -/
theorem eventually_neg_le_ringZeroSum_div_degree (K : ℕ → CharacterRing)
    (hdeg : Tendsto (fun k => ((K k).degree : ℝ)) atTop atTop) (f : ℝ → ℝ)
    (htw : ∀ k, 0 ≤ (K k).twistedSum f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, -ε ≤ ringZeroSum (K k).one_lt (K k).primitive f / (K k).degree := by
  filter_upwards [(tendsto_zeroSum_div_degree K hdeg f).eventually
    (eventually_gt_nhds (show -ε < 0 by linarith))] with k hk
  rw [CharacterRing.ringZeroSum_eq, add_div]
  have := div_nonneg (htw k) (K k).degree_pos.le
  linarith

/-- The same for the pairing: per degree, the limit of jets, counterterms and contacts of the
rings of a tower is eventually at most the pole term per degree plus `ε`. -/
theorem eventually_ringPairing_div_degree_le (K : ℕ → CharacterRing)
    (hdeg : Tendsto (fun k => ((K k).degree : ℝ)) atTop atTop) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {L : ℕ} (hL : 1 ≤ L)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log L ≤ u → f u = 0)
    (htw : ∀ k, 0 ≤ (K k).twistedSum f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∃ l : ℝ,
      Tendsto (fun N : ℕ => ringForm (K k).χ f (3 * L) N +
        2 * weightedContact (ringWeight (K k).χ) f (3 * L) N) atTop (𝓝 l) ∧
      l / (K k).degree ≤
        2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) / (K k).degree +
          ε := by
  filter_upwards [eventually_neg_le_ringZeroSum_div_degree K hdeg f htw hε] with k hk
  refine ⟨_, tendsto_ringForm_add_contact (K k).one_lt (K k).primitive hf hfc hL hsupp, ?_⟩
  rw [sub_div]
  linarith

/-! ### The cyclotomic tower -/

/-- Below `p` no integer `k ≥ 2` is the norm of an ideal of the cyclotomic ring of conductor
`p`: the contact weight vanishes. -/
theorem cyclotomicWeight_eq_zero_of_lt {p : ℕ} [Fact p.Prime] {k : ℕ} (hk2 : 2 ≤ k)
    (hkp : k < p) : cyclotomicWeight p k = 0 := by
  have hp : p.Prime := Fact.out
  have h1 : (k : ZMod p) ≠ 1 := by
    intro h
    have h' : (k : ZMod p) = ((1 : ℕ) : ZMod p) := by rw [h, Nat.cast_one]
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hkp, Nat.mod_eq_of_lt hp.one_lt] at h'
    omega
  have h0 : (k : ZMod p) ≠ 0 := by
    intro h
    have hdvd := (ZMod.natCast_eq_zero_iff k p).mp h
    exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  rw [cyclotomicWeight, if_neg h1, if_neg h0]

/-- **Beyond the window the cyclotomic ring has no contact.** -/
theorem weightedContact_cyclotomicWeight_eq_zero {p : ℕ} [Fact p.Prime] {L : ℕ} (hL : L < p)
    (f : ℝ → ℝ) (N : ℕ) : weightedContact (cyclotomicWeight p) f L N = 0 := by
  unfold weightedContact
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  rw [cyclotomicWeight_eq_zero_of_lt hk'.1 (lt_of_le_of_lt hk'.2 hL), zero_div, zero_mul]

/-- **The defect of a cyclotomic ring beyond the window is archimedean and ramified.** With
`A` the finite part of the jets of the integers on the packet, for every prime `p` beyond the
window the sum over the zeros of the zeta function of the cyclotomic ring of conductor `p` is
`2 d₁ d₂ − (p − 1)A`, plus the energies of the complex places, plus `(p − 2) log p ∫f²`. -/
theorem exists_cyclotomicZeroSum_eq (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K : ℕ}
    (hK : 1 ≤ K) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    ∃ A : ℝ, Tendsto (degreeForm f (3 * K)) atTop (𝓝 A) ∧
      ∀ (p : ℕ) [Fact p.Prime], 3 * K < p →
        cyclotomicZeroSum p f =
          2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
            ((p : ℝ) - 1) * A +
            ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1}, placeEnergy χ.1 (fun u => (f u : ℂ)) +
            ((p : ℝ) - 2) * Real.log p * ∫ u, f u ^ 2 := by
  obtain ⟨A, hA⟩ : ∃ A, Tendsto (degreeForm f (3 * K)) atTop (𝓝 A) :=
    ⟨_, tendsto_degreeForm hf hfc hK hsupp⟩
  refine ⟨A, hA, fun p _ hp => ?_⟩
  have h1 : Tendsto (cyclotomicForm p f (3 * K)) atTop
      (𝓝 (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        cyclotomicZeroSum p f)) :=
    (tendsto_cyclotomicForm_add_contact (p := p) hf hfc hK hsupp).congr fun N => by
      rw [weightedContact_cyclotomicWeight_eq_zero hp, mul_zero, add_zero]
  have hJ := tendsto_finsetSum (Finset.univ : Finset {χ : DirichletCharacter ℂ p // χ ≠ 1})
    fun χ _ => tendsto_placeJet χ.1 hf hfc hK hsupp
  have hM := tendsto_degreeMass hf.continuous hK hsupp
  have h2 : Tendsto (cyclotomicForm p f (3 * K)) atTop
      (𝓝 (((p : ℝ) - 1) * A -
        ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1}, placeEnergy χ.1 (fun u => (f u : ℂ)) -
        ((p : ℝ) - 2) * Real.log p * ∫ u, f u ^ 2)) :=
    (((hA.const_mul ((p : ℝ) - 1)).sub hJ).sub
      (hM.const_mul (((p : ℝ) - 2) * Real.log p))).congr fun N => by
        rw [cyclotomicForm_eq]
  have h := tendsto_nhds_unique h1 h2
  linarith

/-- **The inequality on a fixed packet holds in the cyclotomic tower for all large conductors,
and the defect per degree grows with the root discriminant.** There is `C`, depending on the
packet, such that for every prime `p` beyond the window the sum over the zeros of the zeta
function of the cyclotomic ring of conductor `p` is at least `(p − 1)(½ log p ∫f² − C)`. -/
theorem exists_forall_cyclotomicZeroSum_ge (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {K : ℕ} (hK : 1 ≤ K) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    ∃ C : ℝ, ∀ (p : ℕ) [Fact p.Prime], 3 * K < p →
      ((p : ℝ) - 1) * (Real.log p / 2 * (∫ u, f u ^ 2) - C) ≤ cyclotomicZeroSum p f := by
  obtain ⟨A, -, hA⟩ := exists_cyclotomicZeroSum_eq hf hfc hK hsupp
  set D := 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) with hD
  refine ⟨|A| + |D|, fun p _ hp => ?_⟩
  rw [hA p hp]
  have hp3 : (3 : ℝ) ≤ p := by
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hm : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hPE : 0 ≤ ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1},
      placeEnergy χ.1 (fun u => (f u : ℂ)) :=
    Finset.sum_nonneg fun χ _ => placeEnergy_nonneg χ.1 _
  have hlm : 0 ≤ Real.log p * ∫ u, f u ^ 2 := mul_nonneg hlog hm
  have h1 : ((p : ℝ) - 1) * (Real.log p / 2 * ∫ u, f u ^ 2) ≤
      ((p : ℝ) - 2) * Real.log p * ∫ u, f u ^ 2 := by
    have hhalf : ((p : ℝ) - 1) / 2 ≤ (p : ℝ) - 2 := by linarith
    have := mul_le_mul_of_nonneg_right hhalf hlm
    linarith
  have h2 : -(((p : ℝ) - 1) * |A|) ≤ -(((p : ℝ) - 1) * A) := by
    have := mul_le_mul_of_nonneg_left (le_abs_self A) (show (0 : ℝ) ≤ (p : ℝ) - 1 by linarith)
    linarith
  have h3 : -(((p : ℝ) - 1) * |D|) ≤ D := by
    have h4 : |D| ≤ ((p : ℝ) - 1) * |D| := by
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (p : ℝ) - 1 by linarith) (abs_nonneg D)
      linarith
    linarith [neg_abs_le D]
  linarith

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
