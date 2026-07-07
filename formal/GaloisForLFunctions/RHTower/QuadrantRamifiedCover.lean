/-
The quadrant-ramified cover: local model, deck-charge pullback, and the functoriality no-go.

A local cyclic cover of index `n` is the map `w ↦ ρ + wⁿ`, ramified at `w = 0` over the base point
`ρ`.  Pulling a carrier `f` back through it multiplies the vanishing order — hence the deck charge — at
that point by `n` (`analyticOrderAt_ram_pullback`, `ramCharge_pullback`): this is the local model
(Deliverable 1) and the pullback formula (Deliverable 2).

The point of the phase is to defeat the mod-4 blindness of FE/conjugation-symmetric packets by a cover
that ramifies over *one* quadrant of a V₄-orbit `{ρ, 1−ρ, ρ̄, 1−ρ̄}` and not the aggregate.  The no-go
(Deliverable 3) rules this out: any ramification datum functorial under the functional equation
`s ↦ 1−s` or Schwarz conjugation `s ↦ s̄` is constant on the corresponding orbit
(`no_singleton_ramification_fe`, `quadrant_ram_forced_equal`), so its aggregate charge over a V₄-orbit
is `4·(ram ρ)` — invisible at every rung `j ≤ 2` (`quadrant_ram_charge_blind`).  A cover functorial
under FE/conjugation therefore carries no more quadrant-local information than the symmetric packet it
was meant to beat: the construction fails at its stated purpose, forcing the program toward torsion
seam arithmetic.
-/
import GaloisForLFunctions.RHTower.XiDeck
import GaloisForLFunctions.RHTower.DeckChargeCalculus

open Complex Filter Topology

namespace RHTower

/-! ### The local model and the pullback formula -/

/-- The vanishing order of the monomial `wʲ` at `0` is `j`. -/
theorem analyticOrderAt_id_pow (j : ℕ) : analyticOrderAt (fun w : ℂ => w ^ j) 0 = (j : ℕ∞) := by
  have hid : analyticOrderAt (id : ℂ → ℂ) 0 = 1 :=
    analyticAt_id.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp) (by simp)
  have hpe : (fun w : ℂ => w ^ j) = (id : ℂ → ℂ) ^ j := by funext w; rfl
  rw [hpe, analyticOrderAt_pow analyticAt_id j, hid, nsmul_eq_mul, mul_one]

/-- **Pullback of vanishing order under a ramified cover.**  Pulling an entire carrier `f` back through
the local cyclic cover `w ↦ ρ + wⁿ` (ramified of index `n` over `ρ`) multiplies the vanishing order at
the branch point by `n`: `ord₀ (f ∘ (ρ + ·ⁿ)) = n · ord_ρ f`.  Mechanism: peel `f = (·−ρ)^m·h`, so
`f(ρ + wⁿ) = w^{nm}·h(ρ + wⁿ)` with the cofactor nonzero at `0`. -/
theorem analyticOrderAt_ram_pullback {f : ℂ → ℂ} {ρ : ℂ} {n : ℕ} (hn : 0 < n)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hne : analyticOrderAt f ρ ≠ ⊤) :
    (analyticOrderAt (fun w => f (ρ + w ^ n)) 0).toNat = n * (analyticOrderAt f ρ).toNat := by
  set m : ℕ := (analyticOrderAt f ρ).toNat with hm_def
  have hcoe : analyticOrderAt f ρ = (m : ℕ∞) := (ENat.coe_toNat hne).symm
  obtain ⟨h, hhan, hh0, hfact, -⟩ := exists_peel isOpen_univ hf (Set.mem_univ ρ) hcoe
  have hcomp : (fun w => f (ρ + w ^ n)) = (fun w : ℂ => w ^ (n * m)) * (fun w => h (ρ + w ^ n)) := by
    funext w
    show f (ρ + w ^ n) = w ^ (n * m) * h (ρ + w ^ n)
    rw [hfact (ρ + w ^ n) (Set.mem_univ _), show (ρ + w ^ n - ρ : ℂ) = w ^ n by ring,
      ← pow_mul, mul_comm n m, pow_mul]
  have hpow_an : AnalyticAt ℂ (fun w : ℂ => w ^ (n * m)) 0 := analyticAt_id.pow _
  have hgc : AnalyticAt ℂ (fun w : ℂ => ρ + w ^ n) 0 := analyticAt_const.add (analyticAt_id.pow _)
  have hh_an : AnalyticAt ℂ (fun w : ℂ => h (ρ + w ^ n)) 0 := by
    have := AnalyticAt.comp (g := h) (f := fun w : ℂ => ρ + w ^ n)
      (by rw [show (fun w : ℂ => ρ + w ^ n) 0 = ρ by simp [zero_pow hn.ne']]
          exact hhan ρ (Set.mem_univ ρ)) hgc
    simpa [Function.comp] using this
  have hh0' : (fun w : ℂ => h (ρ + w ^ n)) 0 ≠ 0 := by
    show h (ρ + (0 : ℂ) ^ n) ≠ 0; rw [zero_pow hn.ne', add_zero]; exact hh0
  have hh_ord : analyticOrderAt (fun w : ℂ => h (ρ + w ^ n)) 0 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hh0')
  rw [hcomp, analyticOrderAt_mul hpow_an hh_an, hh_ord, add_zero, analyticOrderAt_id_pow]
  simp

/-- **Pullback formula for the deck charge.**  The rung-`k` deck charge pulls back through the
index-`n` ramified cover by multiplication by `n`: `w_k(f ∘ (ρ + ·ⁿ) at 0) = n · w_k(f at ρ)`. -/
theorem ramCharge_pullback (k : ℕ) {f : ℂ → ℂ} {ρ : ℂ} {n : ℕ} (hn : 0 < n)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hne : analyticOrderAt f ρ ≠ ⊤) :
    wCharge (2 ^ k) ((analyticOrderAt (fun w => f (ρ + w ^ n)) 0).toNat : ℤ)
      = n • wCharge (2 ^ k) ((analyticOrderAt f ρ).toNat : ℤ) := by
  rw [analyticOrderAt_ram_pullback hn hf hne,
    show ((n * (analyticOrderAt f ρ).toNat : ℕ) : ℤ)
      = (n : ℤ) * ((analyticOrderAt f ρ).toNat : ℤ) by push_cast; ring,
    wCharge_nsmul]

/-! ### The functoriality no-go -/

/-- **Equivariant ramification is constant on orbits.**  The abstract no-go: if a ramification datum
`ram` is invariant under a group action (functorial under the symmetry), it takes the same value at
every point of an orbit.  A cover functorial under a symmetry group therefore cannot ramify over one
point of an orbit but not its translates — ramification is an orbit-level, not point-level, property. -/
theorem ram_constant_on_orbit {G α : Type*} [Group G] [MulAction G α] {ram : α → ℕ}
    (hinv : ∀ (g : G) (a : α), ram (g • a) = ram a) {a b : α} (hab : b ∈ MulAction.orbit G a) :
    ram b = ram a := by
  obtain ⟨g, hg⟩ := hab; rw [← hg]; exact hinv g a

/-- **No singleton ramification under the functional equation.**  A ramification datum invariant under
the FE involution `s ↦ 1−s` takes the same value at `ρ` and at the distinct point `1−ρ` (whenever `ρ`
is off the critical line): the cover ramifies over the whole FE-pair, never over `ρ` alone. -/
theorem no_singleton_ramification_fe {ram : ℂ → ℕ} {ρ : ℂ} (hoff : ρ.re ≠ 1 / 2)
    (hFE : ∀ z, ram (1 - z) = ram z) :
    ram (1 - ρ) = ram ρ ∧ (1 - ρ) ≠ ρ := by
  refine ⟨hFE ρ, ?_⟩
  intro h
  apply hoff
  have hr := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.one_re] at hr
  linarith

/-- **No singleton ramification under Schwarz conjugation.**  A conjugation-invariant ramification
datum takes the same value at `ρ` and at the distinct point `ρ̄` (whenever `ρ` is off the real axis). -/
theorem no_singleton_ramification_conj {ram : ℂ → ℕ} {ρ : ℂ} (hoff : ρ.im ≠ 0)
    (hconj : ∀ z, ram ((starRingEnd ℂ) z) = ram z) :
    ram ((starRingEnd ℂ) ρ) = ram ρ ∧ (starRingEnd ℂ) ρ ≠ ρ := by
  refine ⟨hconj ρ, ?_⟩
  intro h
  apply hoff
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

/-- **The four quadrant ramification values are forced equal.**  A ramification datum invariant under
both the FE `s ↦ 1−s` and Schwarz conjugation `s ↦ s̄` takes the same value on the whole V₄-orbit
`{ρ, 1−ρ, ρ̄, 1−ρ̄}`.  Hence no cover functorial under FE/conjugation ramifies over one quadrant but not
the aggregate — quadrant-local ramification is incompatible with FE/conjugation functoriality. -/
theorem quadrant_ram_forced_equal {ram : ℂ → ℕ} (ρ : ℂ)
    (hFE : ∀ z, ram (1 - z) = ram z) (hconj : ∀ z, ram ((starRingEnd ℂ) z) = ram z) :
    ram (1 - ρ) = ram ρ ∧ ram ((starRingEnd ℂ) ρ) = ram ρ ∧
      ram (1 - (starRingEnd ℂ) ρ) = ram ρ := by
  refine ⟨hFE ρ, hconj ρ, ?_⟩
  rw [hFE ((starRingEnd ℂ) ρ), hconj ρ]

/-- **The V₄-functorial cover reproduces the mod-4 blindness.**  Its aggregate ramification charge over
a V₄-orbit is `4·(ram ρ)`, which is invisible at every rung `j ≤ 2`: the cover carries no more
information about the quadrant-local defect than the symmetric packet it was meant to defeat.  This is
the no-go with teeth — the construction fails at its stated purpose, forcing torsion seam arithmetic. -/
theorem quadrant_ram_charge_blind {ram : ℂ → ℕ} (ρ : ℂ)
    (hFE : ∀ z, ram (1 - z) = ram z) (hconj : ∀ z, ram ((starRingEnd ℂ) z) = ram z)
    {j : ℕ} (hj : j ≤ 2) :
    wCharge (2 ^ j) ((ram ρ + ram (1 - ρ) + ram ((starRingEnd ℂ) ρ)
      + ram (1 - (starRingEnd ℂ) ρ) : ℕ) : ℤ) = 0 := by
  haveI : NeZero (2 ^ j) := ⟨pow_ne_zero j (by norm_num)⟩
  obtain ⟨h1, h2, h3⟩ := quadrant_ram_forced_equal ρ hFE hconj
  rw [h1, h2, h3, wCharge_eq_zero_iff, show (ram ρ + ram ρ + ram ρ + ram ρ : ℕ) = 4 * ram ρ by ring]
  have hdvd4 : (2 : ℤ) ^ j ∣ 4 := by simpa using pow_dvd_pow (2 : ℤ) hj
  push_cast
  exact Dvd.dvd.mul_right hdvd4 _

end RHTower
