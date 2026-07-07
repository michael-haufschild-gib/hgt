import GaloisForLFunctions.EulerProduct

/-!
# The pre-spectral firewall as an explicit genuine/fake separation

`EulerProduct` proves the First Theorem (`isMultiplicative_iff_bohr_factorization`) and, separately,
that the Davenport–Heilbronn-style fake coefficient is not multiplicative
(`davenportHeilbronnFakeCoeff_not_isMultiplicative`).  This file composes them into the single
separation the firewall is about: every genuine (multiplicative) Dirichlet coefficient Bohr-factors
over the primes, while the fake fails to — witnessed at a finite `n`, before any zero is examined.
-/

open scoped BigOperators
open ArithmeticFunction

namespace GaloisForLFunctions

/-- **The pre-spectral firewall, as a separation.**  For every genuine (multiplicative) Dirichlet
coefficient function `f`, the Bohr lift factors over the primes at every `n`; yet the
Davenport–Heilbronn-style fake coefficient fails that factorization at some finite `n`.  The Euler
product / Bohr factorization property separates the genuine from the fake, pre-spectrally — no zero is
examined. -/
theorem euler_firewall_separation {f : ArithmeticFunction ℂ} (hf : f.IsMultiplicative) :
    (∀ n : ℕ, n ≠ 0 → f n = n.factorization.prod fun p k => f (p ^ k))
    ∧ (∃ n : ℕ, n ≠ 0 ∧
        davenportHeilbronnFakeCoeff n
          ≠ n.factorization.prod fun p k => davenportHeilbronnFakeCoeff (p ^ k)) :=
  ⟨((isMultiplicative_iff_bohr_factorization f).mp hf).2,
    fake_fails_factorization davenportHeilbronnFakeCoeff
      (by unfold davenportHeilbronnFakeCoeff; norm_num [davenportHeilbronnFakeCoeffInt])
      davenportHeilbronnFakeCoeff_not_isMultiplicative⟩

end GaloisForLFunctions
