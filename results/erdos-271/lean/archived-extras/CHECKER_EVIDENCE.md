# External checker evidence for the Erdős #271 rev-5 release

**Checker:** the Delegate "Check a Lean Proof" service, Lean 4.35.0 / Mathlib 4.35.0. All jobs below ran in the same checker environment:

`environment_hash = a82a201431265fd7641f14022031e301827a6bfc0901ffd05cdc848612faf40a`

**Re-fetched** means Claude fetched the job result directly on 2026-10-21 and confirmed three things:
- `verdict = verified`, `reason_code = proof_verified`;
- the environment hash above;
- `statement_sha256` and `proof_sha256` equal to the sha256 of the files in this archive.

Commands for checking the hashes against the files: `sha256sum rev5/checker-bundles/*` and `sha256sum extras/*/*.lean`.

## Bundles shipped in `rev5/checker-bundles/`

| bundle | content | job id | statement sha256 | proof sha256 | checked |
|---|---|---|---|---|---|
| B1 | Lemma 2 chain (`lemma2_full`) | `12d68ccd-1ef8-4743-9542-558f90d39095` | `3dcb27598dd381d9a3a1ec520040ff14788472f2738e840d6747ac3c5eb341a6` | `8d9c04554e611cc6bc7290681192251a994dded347de5768d84da671c1a16339` | re-fetched |
| B2 | Lemma 4, integral level (`lemma4_integral`) | `8bb31a5d-8abd-457e-960f-7cd58a8b5a9a` | `ead31251a3e13accf7ce20900100c6878f73471b2b98ed3da1d52085b85a5bdd` | `96d01bd1a95c13fb70944c47626020b545c3f52a475de881dececc04358c723d` | re-fetched |
| B4 | `liminf_construction`, 53√3/48 (768 certificate) | `0e2507a5-929a-46fe-b9fa-21e113b4fc09` | `910d1694779b5058d3dd3f5bbe4d7896c38d3704fcd2d48a5281372dceb894f6` | `eca8a9928d48e5b6326125f255b6857256001fe0885757808e691a9fd98ff149` | re-fetched |
| B5 | finite weighted integral identity | `2c4ac1f1-2c06-4b7a-b6a5-5f2068dfeb30` | `374514dcab31798eb0a98e9a82c54ed35e4622cc8cda036775aa6cd474883594` | `0087a2454e34510b31388ad5b261df9293e4efd4b359bac5c9468bec7f1cdb52` | re-fetched |
| B6 | `lemma4_concrete` | `9c47830d-97b2-456e-9823-41a016641203` | `64f9f246b5a0f11528679b3c98c85aeae60bae8b01ec99d7c6f01edbe9dedcd0` | `76c726b2f439511459ff0b57ae14b7c8b793b42ca9c556797be33002ee10948e` | re-fetched |
| B7 | `log_window_bound` (S6 → C7) | `1bc6a346-9b8a-4715-8998-f60d1a2ba660` | `33ec85e89e1dadec538ec8836f94a0a1696cabd8b15d9f59e88a1c58dc62e193` | `69dcf6a12c22d65a65b6f084e7e6e4ecddf48284347242230bc04a6090145aac` | re-fetched |
| B8a | `h61_holds` (S1 → S5 → C7 → C8a) | `95d37d24-724a-440d-918f-6b9720a8e10c` | `ed41ac1a711c7c022f84fb8571271aa96475e15bdc26c8c86fbb3d18963c241c` | `ae5634ee472f945f87dd540c67b1734692e2cceb610c752be25ab7db6b41b4b4` | re-fetched |
| B8b | `erdos271_limsup` + a_k form (C8a → C8) | `11e1017d-26d4-44e1-85f6-b3c66e39fb13` | `9aaa15e846915a3a4327150adfe42dafa450f4ead9c8b479d17a8c4b0a633f16` | `ec2e7ac1e6aefeb23df255d42335c49786f38ad94bd8d8a1d8758fdcf6c845a9` | re-fetched |
| B9 | general S + Stanley wrappers (C8 → C9) | `5aa7dd5e-c857-4cab-b00a-6fd3bd640c69` | `fd0870189b96767e07f87e64e56f426d15c69983ceff3199569ad27bde1074f9` | `7969c431de1a1962c17d11b691a9ab3d47502733cb243e672870cf8ea8b55a16` | re-fetched |
| b16 | 17/6, universal form | `7f84be19-b98e-494f-a96a-6b0a862c62a3` | `cf6d045e5e58cd74575ec313554031ab1b538cbfb9331234ba9c642f983253f9` | `dde7fee077b70e99094aef733c3eace864264fb8a9005eaca3369222d370be96` | re-fetched |
| b16e | 17/6, existence form | `e343345f-df21-4d0a-a9bd-bd7fc0fe4267` | `609db29cae7395099d0fb2da7b9da47223accc7645d06920184132970b208048` | `aa1c615fdfd6fc9be1736c6062f3039358ea7f6a869dc299045a8bd82951cc4e` | re-fetched |

## Files in `extras/`

| item | job id | statement sha256 | proof sha256 | checked |
|---|---|---|---|---|
| C\* gluing: (B1→B5→B6→B7→B8a→B8b→B9→C9) | `68fdc6fb-0c74-4be9-a243-8d7f6ad400ef` | `5aacdcf13d10ed495a33054b6e562a89638f634160f21071a9a7eabcceafac5a` | `3f386422a6a03e67fb29ee9b2f7d03f877705462651c4d8003fc07bbfa2ec0dc` | submitted by Claude; resubmitted independently by Grok as job `e0c9847a` (verified) |
| liminf 419√3/384, strong covering, single term | `d5e58222…` | `186d2fca388dcac7af878d7c1c9562fe2ff90dd64c843e4344fda5c9334812a1` | `6eeeb6ab23cc160fe52f79450691fdcd65900a7ed7f4addbcf31ecce0f6f80fe` | submitted by Claude (round 33). Also compiled locally by Grok, axioms `propext`, `Classical.choice`, `Quot.sound` |
| liminf 1675√3/1536 (not in rev 5) | `042a1cf7-e251-4071-90f5-b1f384498329` | `f34ea2a577ba67182a137abd724314a1680934c5b5e52e9886a1145a90589836` | `4cab2175f543161e3fff9819fb22bf70aa39920232f83be2bfbec39009ef81b3` | re-fetched. Also compiled locally by Grok with the standard axioms |

## Reading the evidence correctly
- **C\* end to end [EXT-chain]:** B1, B5–B9 and the gluing job give C9 by modus ponens across 8 verdicts in one environment. C9 is the statement of `ComposedC9.composed` in `rev5/Composed.lean`.
- **Not one kernel check:** a single-term C9 was rejected for exceeding the default `maxHeartbeats`. That was Grok's job `bb93cb63`, about 483k heartbeats in total.
- **No axioms reported:** the checker does not list axioms. The standard-axiom claim rests on `#print axioms` in the full build (`VERIFY.md` §3).
