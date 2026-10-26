# NBA Edge

One Python script pulls NBA data from free public sources, models every game for the
next 7 days, and writes `nba_dashboard.html`. After each run it publishes the page to
GitHub Pages: **https://halfwitty.github.io/NBADashboard/**

## Setup (once)

```
pip install requests numpy pyarrow
```

Python 3.9 or newer. Git is needed for publishing (see below).

## Run

```
python nba_edge.py
```

That builds the board and publishes it. Add `--open` to also open it in your browser.

- The **first run** downloads two seasons of box scores (about 3 MB) plus a summary for
  each game played so far this season. Expect a minute or two.
- After that, each run only pulls what's new (seconds).
- Data is cached in `nba_data/` next to the script. Delete that folder to start fresh
  (this also clears the track record).

Run it again close to tip-off: lines, prop prices and the injury report change all day.

Options:

| Flag | What it does |
|---|---|
| `--open` | Open the dashboard in your browser when done |
| `--days 3` | Show fewer or more days (default 7: the betting week) |
| `--date 2026-11-02` | Build the board starting on another date |
| `--no-publish` | Build locally without pushing to GitHub |
| `--offline` | Rebuild from cached data without downloading |
| `--no-odds` | Ignore sportsbook prices |
| `--no-props` | Skip fetching player prop prices |
| `--no-injuries` | Skip the injury report |
| `--out path.html` | Write the dashboard somewhere else |

## What's on the dashboard

- **Top bets**: the best 5-10 bets of the week across moneylines, spreads, totals and
  player props, mixing high-probability picks with the biggest edges. Each one has a
  price bar showing where it's a deal, thin, or a pass, with the book's price marked.
  Below that: model lines for games that don't have a line yet (and the number to bet
  each side at), props to price-check, and big model vs market gaps to investigate.
- **Matchups**: every game, filterable by day. Open a game for:
  - *How to bet it*: the side, moneyline, total and best props in plain language
  - the betting board: moneyline, spread, total, team totals, 1st half and 1st quarter,
    each with our probability, the market's, fair odds and a "bet at" price; type your
    book's price (and line) to see the expected return
  - injuries with what each absence is worth
  - projected minutes for every rotation player (with last-5 and season minutes) and
    projections for points, rebounds, assists, threes and PRA
  - form: last 5, record, home/road, against the spread, over/under, rest, roster change,
    head to head
  - about 20 stats with league ranks
- **Props**: every player this week, any stat (including PRA, P+R, P+A, R+A), sortable,
  with a calculator for any line and price.
- **Injuries**, **Standings** (with model ratings, ATS and O/U records), **Track record**
  and **How it works**.

## Reading the odds

For every bet you get:

- **Fair**: the break-even price for our probability. Worse than this, pass.
- **Bet at**: the price where the bet is still +EV even if we're a bit optimistic.
  At this price or better = value. Between Bet at and Fair = lean.
- **Your price**: type your sportsbook's price (e.g. `-135` or `+150`) to see the
  expected return and a Value / Lean / Avoid tag.

## How good is it?

Tested on the 2025-26 season (walk-forward, no peeking):

- Spreads: the model alone missed final margins by 13.6 points (root mean square) vs 13.5
  for closing lines on 554 games; a 35% model / 65% market blend beat both. That blend is
  what the board uses when a line is posted. When the model disagreed with the closing
  spread by 3+ points, its side covered 54.8% (109-90), with perfect knowledge of who
  played, so treat real-world edges as thinner.
- Totals: closing lines were clearly better than the model, so the model only nudges
  totals (20% weight). Expect few totals in the top bets.
- Props: projections beat a last-10-games average on points, rebounds, assists and PRA,
  and the over/under probabilities were calibrated on 2025-26 results.

Watch the Track record tab for a few weeks before trusting any one market.

## Publishing to GitHub Pages (one-time setup)

1. Install git (https://git-scm.com) and make sure you can push to GitHub from this
   computer. Easiest: install the GitHub CLI and run `gh auth login`, or let Git
   Credential Manager sign you in the first time it asks.
2. Run the script once. It clones the repo into `nba_site/` next to the script and
   pushes `index.html`.
3. On GitHub: repo **Settings -> Pages -> Build and deployment**: Source "Deploy from a
   branch", branch `main`, folder `/ (root)`, Save.

After that, every run updates the page within a minute or two. Each day's board is also
kept at `history/YYYY-MM-DD.html`. Use `--no-publish` to skip pushing, or set
`"repo_url": ""` in `CONFIG` to turn publishing off. Only the dashboard is published;
your cached data and prediction log stay on your computer.

On a free GitHub account, Pages sites are public, so anyone with the link can see the board.

## Run it automatically

Windows: Task Scheduler -> Create Basic Task -> Daily -> Start a program:
`python`, arguments `nba_edge.py`, start in: the script's folder. Add a second trigger
around 5 PM ET so the board has the day's final injury news.

macOS/Linux (cron, 10am and 5pm every day):
```
0 10,17 * * * cd /path/to/folder && /usr/bin/python3 nba_edge.py
```

## Tuning

Settings are in `CONFIG` at the top of `nba_edge.py`, for example `hl_days` (how fast
form fades), `prior_games` and `prior_regress` (how much last season counts),
`w_model_margin` / `w_model_total` (model vs market blend), `inj_k` (injury impact),
and for top bets `top_bets_max`, `high_prob_min`, `min_ev_top`, `max_props_top`,
`max_market_gap`.

## Data sources

- Box scores: ESPN, via the sportsdataverse data releases on GitHub
  (`sportsdataverse/sportsdataverse-data`), topped up from ESPN game summaries
- Schedule, sportsbook lines, prop prices, injuries, rosters: ESPN's public API

If a run prints "Sportsbook lines found for 0 of N games" while lines are posted, or
"Player prop prices found: 0" for games with props, send the files in `nba_data/misc`
and `nba_data/scoreboards` so the parser can be adjusted.

## Before you bet

Late scratches and rest days announced at shootaround aren't known until the injury
report updates; run the script again close to tip-off. Nothing here is financial advice.
Bet only what you can afford to lose.
