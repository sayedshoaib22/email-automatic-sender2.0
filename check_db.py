import sqlite3

conn = sqlite3.connect("mailer.db")
cursor = conn.cursor()

# show all tables
cursor.execute("SELECT name FROM sqlite_master WHERE type='table'")
tables = cursor.fetchall()
print("Tables:", tables)

# show sent_emails data
cursor.execute("SELECT * FROM sent_emails")
print("\nSent Emails:")
for row in cursor.fetchall():
    print(row)

# show recovery_state data
cursor.execute("SELECT * FROM recovery_state")
print("\nRecovery State:")
for row in cursor.fetchall():
    print(row)

conn.close()
