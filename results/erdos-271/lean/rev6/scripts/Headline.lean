import Audit.Final
import Audit.Final61
import Audit.AkForm
import Audit.General
import Audit.Stanley
import IndependentEndgame
import LiminfGen
import LiminfFinal
import Liminf
import B16Limsup
import Composed
import WeightedIdentity
import Liminf1675

set_option pp.proofs false

/-! ## (a) Universal limsup lower bound C* — Grok's final assembly -/
#check @Erdos271.Final.erdos271_limsup
#print axioms Erdos271.Final.erdos271_limsup
#check @Erdos271.Final.erdos271_ak
#print axioms Erdos271.Final.erdos271_ak
#check @Erdos271.Final.erdos271_limsup_any
#print axioms Erdos271.Final.erdos271_limsup_any
#check @Erdos271.Final.erdos271_limsup_ge_any
#print axioms Erdos271.Final.erdos271_limsup_ge_any
#check @Erdos271.Final.erdos271_ak_any
#print axioms Erdos271.Final.erdos271_ak_any
#check @Erdos271.Stanley.stanley_limsup
#print axioms Erdos271.Stanley.stanley_limsup
#check @Erdos271.Stanley.stanley_ak
#print axioms Erdos271.Stanley.stanley_ak
#check @Erdos271.Stanley.stanley_std_limsup
#print axioms Erdos271.Stanley.stanley_std_limsup
#check @Erdos271.Stanley.stanley_std_ak
#print axioms Erdos271.Stanley.stanley_std_ak
#check @Erdos271.Stanley.two_seed_limsup
#print axioms Erdos271.Stanley.two_seed_limsup
#check @Erdos271.Stanley.two_seed_ak
#print axioms Erdos271.Stanley.two_seed_ak

/-! ## (a') Universal limsup lower bound C* — ChatGPT's independent final assembly -/
#check @Erdos271.IndependentEndgame.arbitrarily_large_witnesses
#print axioms Erdos271.IndependentEndgame.arbitrarily_large_witnesses
#check @Erdos271.IndependentEndgame.fixed_error_budget
#print axioms Erdos271.IndependentEndgame.fixed_error_budget

/-! ## (b) Liminf construction — generic theorem and instances -/
#check @Erdos271.Liminf.StaticCert.liminf_of_cert
#print axioms Erdos271.Liminf.StaticCert.liminf_of_cert
#check @Erdos271.Liminf.liminf_construction_1889
#print axioms Erdos271.Liminf.liminf_construction_1889
#check @Erdos271.Liminf.liminf_construction_1894
#print axioms Erdos271.Liminf.liminf_construction_1894
#check @Erdos271.Liminf.liminf_construction_1912
#print axioms Erdos271.Liminf.liminf_construction_1912
#check @Erdos271.Liminf.liminf_construction
#print axioms Erdos271.Liminf.liminf_construction

/-! ## (c) Limsup covering construction 17/6 (base 16) -/
#check @Erdos271.B16.B16_main
#print axioms Erdos271.B16.B16_main
#check @Erdos271.B16.B16_exists
#print axioms Erdos271.B16.B16_exists
#check @Erdos271.B16.mem_iff_blocks
#print axioms Erdos271.B16.mem_iff_blocks
#check @Erdos271.B16.B16_limsup
#print axioms Erdos271.B16.B16_limsup
#check @Erdos271.B16.S16_limsup
#print axioms Erdos271.B16.S16_limsup

/-! ## (d) Exact-bundle composition of the C* checker bundles B1,B5,B6,B7,B8a,B8b,B9 -/
#check @ComposedC9.composed
#print axioms ComposedC9.composed

/-! ## (e) rev 6 candidate additions -/
-- The finite weighted integral identity cited in Paper 1 (checker-verified separately as bundle B5).
#check @Erdos271.FiniteIntegrals.finite_weighted_integral_identity
#print axioms Erdos271.FiniteIntegrals.finite_weighted_integral_identity
-- Claude's 1675*sqrt(3)/1536 liminf term (checker job 042a1cf7), kept separate from liminf_construction_1889.
#check @Erdos271.Liminf1675.liminf_construction_1675
#print axioms Erdos271.Liminf1675.liminf_construction_1675
