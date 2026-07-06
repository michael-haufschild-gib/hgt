/-
The closed-sweep telescope of the ledger chain: a deformation returning to its start has
zero net flux, and a projective sweep decomposes its window against its complement.

Ledger chains concatenate with additive flux.  Transporting local `n`-th roots around a
closed chain — one returning to its starting member — multiplies the deck class by
`exp(2πi·flux/n)`, but root-independence pins that ratio to one, so `n` divides the flux for
every level at which the member admits chart roots.  When the member admits roots at every
level (any function nonvanishing on the simply connected slit charts) the flux is exactly
zero: the net signed multiplicity that crosses the annulus around a closed loop of
deformations is null.

Split a projective sweep at its window: the closed loop is the anchored window chain
followed by its complementary back-sweep, and zero total flux forces the window flux and the
back-sweep flux to agree modulo two.  The parity of the positive-fiber events therefore
equals the parity of the complementary events — the two event classes are one, reducing the
band-edge pairing burden to a single class.
-/
import GaloisForLFunctions.RHTower.LedgerReduction
import GaloisForLFunctions.RHTower.DiscWindow

namespace RHTower

open Complex Metric

/-- `exp(2πi·q/n) = 1` iff `n` divides the integer `q`. -/
theorem exp_two_pi_mul_int_div_eq_one_iff {n : ℕ} (hn : 0 < n) (q : ℤ) :
    exp (2 * (Real.pi : ℂ) * I * (q : ℂ) / n) = 1 ↔ (n : ℤ) ∣ q := by
  rw [Complex.exp_eq_one_iff]
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hπI : (2 : ℂ) * Real.pi * I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  constructor
  · rintro ⟨k, hk⟩
    have h3 : (2 : ℂ) * Real.pi * I * q / n = k * (2 * Real.pi * I) := hk
    field_simp at h3
    have h4 : (2 : ℂ) * Real.pi * I * q = 2 * Real.pi * I * (k * n) := by rw [h3]; ring
    have h2 : (q : ℂ) = k * n := mul_left_cancel₀ hπI h4
    have hqZ : (q : ℤ) = k * n := by exact_mod_cast h2
    exact ⟨k, by linarith⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by push_cast; field_simp⟩

/-- An integer divisible by every positive natural is zero. -/
theorem int_eq_zero_of_forall_pos_nat_dvd {q : ℤ}
    (h : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ q) : q = 0 := by
  by_contra hq
  have hna : q.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hq
  have hd := h (q.natAbs + 1) (by omega)
  have h5 := Int.natAbs_dvd_natAbs.mpr hd
  rw [Int.natAbs_natCast] at h5
  have := Nat.le_of_dvd (by omega) h5
  omega

/-- **Concatenation of ledger chains.**  Chains compose end to start with additive flux:
the net signed multiplicity crossing the annulus over a composite deformation is the sum of
the parts. -/
theorem ledgerChain_trans {a : ℂ} {r₀ R : ℝ} {f g h : ℂ → ℂ} {flux₁ flux₂ : ℤ}
    (h₁ : LedgerChain a r₀ R f g flux₁) (h₂ : LedgerChain a r₀ R g h flux₂) :
    LedgerChain a r₀ R f h (flux₁ + flux₂) := by
  induction h₁ with
  | refl f => simpa using h₂
  | dominated hg hclose rest ih => exact LedgerChain.dominated hg hclose (ih h₂)
  | @jump_in f' g' h' ρ' m L' hρ' hfact rest ih =>
      have : L' + m + flux₂ = L' + flux₂ + m := by ring
      rw [this]
      exact LedgerChain.jump_in hρ' hfact (ih h₂)
  | @jump_out f' g' h' ρ' m L' hρ' hfact rest ih =>
      have : L' - m + flux₂ = L' + flux₂ - m := by ring
      rw [this]
      exact LedgerChain.jump_out hρ' hfact (ih h₂)

/-- A chart root of a function nonzero at a point is nonzero there. -/
private theorem chart_root_ne_zero {G f : ℂ → ℂ} {n : ℕ} (hn : 0 < n) {p : ℂ}
    (hp : G p ^ n = f p) (hf : f p ≠ 0) : G p ≠ 0 := by
  intro h0
  rw [h0, zero_pow hn.ne'] at hp
  exact hf hp.symm

/-- The deck class of a root pair is nonzero when the underlying function is nonzero at the
two basepoints. -/
private theorem deckClass_ne_zero_of_roots {G₁ G₂ f : ℂ → ℂ} {n : ℕ} (hn : 0 < n)
    {pP pM : ℂ} (hpG₁P : G₁ pP ^ n = f pP) (hpG₂P : G₂ pP ^ n = f pP)
    (hpG₁M : G₁ pM ^ n = f pM) (hpG₂M : G₂ pM ^ n = f pM)
    (hfP : f pP ≠ 0) (hfM : f pM ≠ 0) :
    deckClass G₁ G₂ pP pM ≠ 0 := by
  rw [deckClass]
  refine div_ne_zero (div_ne_zero ?_ ?_) (div_ne_zero ?_ ?_)
  · exact chart_root_ne_zero hn hpG₁P hfP
  · exact chart_root_ne_zero hn hpG₂P hfP
  · exact chart_root_ne_zero hn hpG₁M hfM
  · exact chart_root_ne_zero hn hpG₂M hfM

/-- **The closed-sweep divisibility.**  A closed ledger chain — one returning to its
starting member `f` — has flux divisible by every level `n` at which `f` admits local
`n`-th roots on the two slit charts, with `f` nonvanishing at the basepoints: transport
around the loop multiplies the deck class by `exp(2πi·flux/n)`, but root-independence pins
that ratio to one. -/
theorem ledgerChain_closed_flux_dvd {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    {f : ℂ → ℂ} {flux : ℤ} (hchain : LedgerChain a r₀ R f f flux)
    {n : ℕ} (hn : 0 < n) {G₁ G₂ : ℂ → ℂ}
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ n = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ n = f z)
    (hfP : f (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hfM : f (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0) :
    (n : ℤ) ∣ flux := by
  obtain ⟨hPmem, hMmem⟩ := annulus_basepoints_mem h0 hrR
  obtain ⟨H₁, H₂, hH₁, hH₂, hpH₁, hpH₂, hHcls⟩ :=
    ledgerChain_transport h0 hrR hn hchain G₁ G₂ hG₁ hG₂ hpG₁ hpG₂
  -- root independence: transported and original roots of f share their deck class
  have hindep := deckClass_root_indep hn (isOpen_chartRA a r₀ R)
    (isPreconnected_chartRA a h0) (isOpen_chartLA a r₀ R) (isPreconnected_chartLA a h0)
    hG₁ hH₁ hG₂ hH₂ hpG₁ hpH₁ hpG₂ hpH₂
    hPmem.1 hPmem.2 hMmem.1 hMmem.2 hfP hfM
  -- so the exponential factor is one
  have hGne : deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 :=
    deckClass_ne_zero_of_roots hn (hpG₁ _ hPmem.1) (hpG₂ _ hPmem.2)
      (hpG₁ _ hMmem.1) (hpG₂ _ hMmem.2) hfP hfM
  have hexp : exp (2 * (Real.pi : ℂ) * I * (flux : ℂ) / n) = 1 := by
    have h1 : exp (2 * (Real.pi : ℂ) * I * (flux : ℂ) / n) *
        deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
          (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) =
        deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
          (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) := by
      rw [← hHcls, hindep]
    exact mul_right_cancel₀ hGne (by rw [h1, one_mul])
  exact (exp_two_pi_mul_int_div_eq_one_iff hn flux).mp hexp

/-- **The closed sweep has null flux.**  If the starting member of a closed ledger chain
admits chart roots at every level (as any function nonvanishing on the simply connected slit
charts does), the flux is exactly zero: a loop of deformations returning to its start crosses
no net multiplicity through the annulus. -/
theorem ledgerChain_closed_flux_eq_zero {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    {f : ℂ → ℂ} {flux : ℤ} (hchain : LedgerChain a r₀ R f f flux)
    (hroots : ∀ n : ℕ, 0 < n → ∃ G₁ G₂ : ℂ → ℂ,
      AnalyticOnNhd ℂ G₁ (chartRA a r₀ R) ∧ AnalyticOnNhd ℂ G₂ (chartLA a r₀ R) ∧
      (∀ z ∈ chartRA a r₀ R, G₁ z ^ n = f z) ∧ (∀ z ∈ chartLA a r₀ R, G₂ z ^ n = f z))
    (hfP : f (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hfM : f (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0) :
    flux = 0 := by
  apply int_eq_zero_of_forall_pos_nat_dvd
  intro n hn
  obtain ⟨G₁, G₂, hG₁, hG₂, hpG₁, hpG₂⟩ := hroots n hn
  exact ledgerChain_closed_flux_dvd h0 hrR hchain hn hG₁ hG₂ hpG₁ hpG₂ hfP hfM

/-- **The window–complement parity decomposition.**  A projective sweep splits at its
window into an anchored window chain `f → g` and a complementary back-sweep `g → f`.  The
composite is a closed chain, so its flux is even at any level-two root witness of `f`, and
the window flux therefore agrees with the back-sweep flux modulo two: the parity of the
window's crossing events equals the parity of the complement's, collapsing the two event
classes into one. -/
theorem ledgerChain_window_back_two_dvd {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    {f g : ℂ → ℂ} {fluxWin fluxBack : ℤ}
    (hwin : LedgerChain a r₀ R f g fluxWin) (hback : LedgerChain a r₀ R g f fluxBack)
    {G₁ G₂ : ℂ → ℂ}
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 = f z)
    (hfP : f (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hfM : f (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0) :
    (2 : ℤ) ∣ (fluxWin - fluxBack) := by
  have hclosed : LedgerChain a r₀ R f f (fluxWin + fluxBack) := ledgerChain_trans hwin hback
  have hdvd : (2 : ℤ) ∣ (fluxWin + fluxBack) :=
    ledgerChain_closed_flux_dvd h0 hrR hclosed two_pos hG₁ hG₂ hpG₁ hpG₂ hfP hfM
  omega

end RHTower

namespace RHTower

open Complex Metric

/-- **The closed sweep of a factored member has null flux, unconditionally.**  For a member
with an enclosed configuration on the ball — finitely many zeros inside the inner radius and a
zero-free cofactor — the annular charts are simply connected and the member is zero-free
there, so it admits chart roots at every level and the closed-loop flux is exactly zero.  This
is the standard shape of every ledger member: the net multiplicity crossing the annulus over
any deformation loop is null. -/
theorem ledgerChain_closed_flux_eq_zero_of_enclosed {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 < r₀) (hrR : r₀ < R) {f h : ℂ → ℂ} {t : Finset ℂ} {m : ℂ → ℕ} {flux : ℤ}
    (hchain : LedgerChain a r₀ R f f flux)
    (hf : AnalyticOnNhd ℂ f (ball a R))
    (hρ : ∀ w ∈ t, ‖w - a‖ ≤ r₀)
    (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (∏ w ∈ t, (z - w) ^ m w) * h z) :
    flux = 0 := by
  obtain ⟨hneR, _⟩ := enclosed_ne_zero_on_charts hρ hh0 hfact
  obtain ⟨hPmem, hMmem⟩ := annulus_basepoints_mem h0.le hrR
  have hfP : f (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := hneR _ hPmem.1
  have hfM : f (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := hneR _ hMmem.1
  refine ledgerChain_closed_flux_eq_zero h0.le hrR hchain ?_ hfP hfM
  intro n hn
  obtain ⟨⟨G₁, hG₁an, hG₁pow⟩, ⟨G₂, hG₂an, hG₂pow⟩⟩ :=
    exists_annular_roots_of_enclosed h0 hrR hf hρ hh0 hfact hn
  exact ⟨G₁, G₂, hG₁an, hG₂an, hG₁pow, hG₂pow⟩

/-- **Concatenation of event-typed ledger chains.**  Event chains compose by appending their
event lists: the recorded transversal events of a composite deformation are those of the
parts in order. -/
theorem ledgerChainE_trans {a : ℂ} {r₀ R : ℝ} {f g h : ℂ → ℂ} {L₁ L₂ : List ℤ}
    (h₁ : LedgerChainE a r₀ R f g L₁) (h₂ : LedgerChainE a r₀ R g h L₂) :
    LedgerChainE a r₀ R f h (L₁ ++ L₂) := by
  induction h₁ with
  | refl f => simpa using h₂
  | dominated hg hclose rest ih => exact LedgerChainE.dominated hg hclose (ih h₂)
  | @jump_in f' g' h' ρ' m L' hρ' hfact rest ih =>
      rw [List.cons_append]
      exact LedgerChainE.jump_in hρ' hfact (ih h₂)
  | @jump_out f' g' h' ρ' m L' hρ' hfact rest ih =>
      rw [List.cons_append]
      exact LedgerChainE.jump_out hρ' hfact (ih h₂)

end RHTower

namespace RHTower

open Complex Metric

/-- **The event-list parity mirror.**  For an event-typed window chain `f → g` and its
event-typed back-sweep `g → f`, with `f` carrying level-two chart roots, the summed window
events and the summed back-sweep events agree modulo two: the parity of the window's
transversal events equals the parity of the complement's, so the two event classes of the
band-edge pairing collapse to one. -/
theorem ledgerChainE_window_back_two_dvd {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    {f g : ℂ → ℂ} {Lwin Lback : List ℤ}
    (hwin : LedgerChainE a r₀ R f g Lwin) (hback : LedgerChainE a r₀ R g f Lback)
    {G₁ G₂ : ℂ → ℂ}
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 = f z)
    (hfP : f (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hfM : f (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0) :
    (2 : ℤ) ∣ (Lwin.sum - Lback.sum) :=
  ledgerChain_window_back_two_dvd h0 hrR (ledgerChainE_toChain hwin)
    (ledgerChainE_toChain hback) hG₁ hG₂ hpG₁ hpG₂ hfP hfM

end RHTower
